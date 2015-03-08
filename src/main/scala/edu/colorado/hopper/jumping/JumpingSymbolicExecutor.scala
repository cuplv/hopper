package edu.colorado.hopper.jumping

import com.ibm.wala.classLoader.IField
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ssa.{IR, ISSABasicBlock}
import edu.colorado.hopper.executor.{TransferFunctions, UnstructuredSymbolicExecutor}
import edu.colorado.hopper.jumping.JumpingSymbolicExecutor._
import edu.colorado.hopper.state._
import edu.colorado.hopper.util.PtUtil
import edu.colorado.thresher.core.Options
import edu.colorado.walautil.Types.{MSet, WalaBlock}
import edu.colorado.walautil.{ClassUtil, Util}


object JumpingSymbolicExecutor {
  // if true, when we do a piecewise jump and fail, we will continue doing path-based execution
  private def DEBUG = false
}

class DefaultJumpingSymbolicExecutor(override val tf : TransferFunctions,
                                     override val rr : RelevanceRelation,
                                     override val keepLoopConstraints : Boolean = false)
  extends JumpingSymbolicExecutor {}

trait JumpingSymbolicExecutor extends UnstructuredSymbolicExecutor {
  val rr : RelevanceRelation
  
  var jmpNum = 0 
  
  // exposed to allow subclasses to eliminate or conditionalize the unproduceable constraint check
  def hasUnproduceableConstraint(p : Path) : Boolean = rr.hasUnproduceableConstraint(p)

  final def forkToPredecessorBlocksNoJump(instrPaths : List[Path], startBlk : ISSABasicBlock, loopHeader : Option[ISSABasicBlock],
                                          ir : IR, passPaths : List[Path], failPaths : List[Path], test : Path => Boolean) =
    super.forkToPredecessorBlocks(instrPaths, startBlk, loopHeader, ir, passPaths, failPaths, test)

  final def returnFromCallNoJump(p : Path) : Iterable[Path] = super.returnFromCall(p)

  override def forkToPredecessorBlocks(instrPaths : List[Path], startBlk : ISSABasicBlock, loopHeader : Option[ISSABasicBlock],
                                       ir : IR, passPaths : List[Path], failPaths : List[Path], test : Path => Boolean) =
   // disallowing nested jumps for now
   if (instrPaths.forall(p => hasUnproduceableConstraint(p) || (!p.isInJump && piecewiseJumpRefuted(p))))
     (passPaths, failPaths)
   else
     forkToPredecessorBlocksNoJump(instrPaths, startBlk, loopHeader, ir, passPaths, failPaths, test)
  
  var piecewiseInvMap = new InvariantMap[(CGNode,WalaBlock,Int)]
  /** set of fields that we tried to jump because we suspected they were involved in an invariant, but failed to get a
    * refutation */
  val failedObjInvariants : MSet[Set[IField]] = Util.makeSet[Set[IField]]


  // TODO: cleaner, inheritance-independent solution here
  override def getInvariantMaps : List[InvariantMap[_ <: Any]] = piecewiseInvMap :: super.getInvariantMaps
  // replace the current invariant maps with the ones in newMaps
  override def resetInvariantMaps(newMaps : List[InvariantMap[_ <: Any]]) : Unit = {
    this.piecewiseInvMap = newMaps(0).asInstanceOf[InvariantMap[(CGNode,WalaBlock,Int)]] 
    this.callerInvMap = newMaps(1).asInstanceOf[InvariantMap[(CGNode,CGNode)]] 
    this.loopInvMap = newMaps(2).asInstanceOf[InvariantMap[Iterable[(CGNode,ISSABasicBlock)]]]   
  }
  
  override def clearInvariantMaps() : Unit = {
    super.clearInvariantMaps
    piecewiseInvMap.clear
  }

  override def cleanup() = {
    super.cleanup()
    failedObjInvariants.clear()
    rr.cleanup()
  }

  override def cleanup(oldInvMaps : Option[List[InvariantMap  [_]]]) {
    super.cleanup(oldInvMaps)
    failedObjInvariants.clear()
    rr.cleanup
  }
  
  /**
   * @return true if performing a piecewise jump refuted p,
   * false if we decided not to jump or if jump failed to give us a refutation
   */
  def piecewiseJumpRefuted(p : Path) : Boolean =
    shouldJump(p) match {
      case Some((jmpPath, isProducedCallback, failCallback)) =>
        assert(!(jmpPath eq p)) // jmpPath should be a copy of p
        val curJmp = { jmpNum += 1; jmpNum }
        rr.getPiecewisePaths(jmpPath, curJmp) match {
          case Some(unfilteredPiecewisePaths) =>
            val oldInvMaps = if (Options.BACKTRACK_JUMPING) cloneInvariantMaps else Nil
            val piecewisePaths =
              unfilteredPiecewisePaths.filter(p => !piecewiseInvMap.pathEntailsInv((p.node, p.blk, p.index), p))
            if (DEBUG) {
              println("got " + piecewisePaths.size + " piecewise paths:")
              piecewisePaths.foreach(p => print(p.id + "X :" + ClassUtil.pretty(p.node) + ",\n" + p)); println
            }
     
            piecewisePaths.isEmpty || {
              if (DEBUG) println("Performing piecewise jump " + curJmp + " from starting point " + ClassUtil.pretty(p.node))
              // push all piecewise paths backward, taking note of when the invariant the jump was based on is produced
              refutePiecewisePaths(piecewisePaths,
                // this purposely drops the old test() on the floor. this is part of losing all context when we jump,
                // since test() may tell us to stop when we reach a certain basic block (or something similar).
                // however, this may have unexpected results in the case that the user specified test() manually
                p => { if (p.containsJump(curJmp) && isProducedCallback(p.qry)) { p.removeJump(curJmp) }; true },
                     curJmp, failCallback, oldInvMaps)
            }
          case None => false // relevance graph decided not to jump
        }
      case None => false // shouldJump() decided not to jump
    }
  
  override def executeBackward(qry : Qry, test : Option[Path => Boolean]) : Iterable[Path] = {
    // prevent clients from using test() filtering predicate with piecewise execution, since it doesn't work after a jump    
    assert(!test.isDefined, "Piecewise executor ignores test() parameter while jumping!")
    super.executeBackward(qry, test)
  }
  
  /**
   * @return true if all piecewisePaths are refuted, false otherwise
   */
  def refutePiecewisePaths(piecewisePaths : List[Path], test : Path => Boolean, curJmp : Int, 
                           failCallback : Unit => Any, oldInvMaps : List[InvariantMap[_]]) : Boolean = {
    try {                                                         
      // push all piecewise paths backward, taking note of when the invariant the jump was based on is produced
      executeBackwardWhile(piecewisePaths, test) match {
        case newFailPaths =>
          if (DEBUG) println("Done with piecewise jump " + curJmp)
          if (newFailPaths.size == 0 || !newFailPaths.exists(p => p.foundWitness)) {
            if (DEBUG) println("Refuted by piecewise jump " + curJmp + "!")
            true // refuted by piecewise jump!
          } else {
            if (DEBUG) println("got failPaths " + newFailPaths)
            handleFailedJump(oldInvMaps, failCallback, curJmp)                 
          }
      }
    } catch {
      case WitnessFoundException => handleFailedJump(oldInvMaps, failCallback, curJmp)              
      case e : Throwable => throw e
    }  
  }
  
  def handleFailedJump(oldInvMaps : List[InvariantMap[_ <: Any]], callback : Unit => Any, curJmp : Int) : Boolean = {
    if (Options.BACKTRACK_JUMPING) {
      if (DEBUG) println("backtracking after failed piecewise jump " + curJmp)
      // need to reset invariant maps before backtracking or we may get unsound refutations
      this.resetInvariantMaps(oldInvMaps)
      callback() // invoke callback passed to us by shouldJump()
      false
    } else throw WitnessFoundException
  }

  // TODO: cache sets of constraints we've already checked
  // match the first invariant template that we can
  /** @return callback to be called on failure of jump if we should jump, None otherwise */
  def shouldJump(p : Path) : Option[(Path, Qry => Boolean, Unit => Any)] =
    // TODO: we don't allow nested jumps now, can lift this later. really, just don't want to jump to the same spot
    if (!p.qry.hasConstraint || p.isClinitPath(cg) || p.isInJump) None
    else matchesInvariantTemplate(p)
  
  // TODO: extract InvariantTemplate to a class
  val templates : List[Path => Option[(Path, Qry => Boolean, Unit => Any)]] =
    List(objectInvariantTemplate, contextSensitiveTemplate)
  
  /** @return callback to be called on failure of jump if we found a match, None otherwise */
  def matchesInvariantTemplate(p : Path) : Option[(Path, Qry => Boolean, Unit => Any)] = {
    var matched = None : Option[(Path, Qry => Boolean, Unit => Any)]
    templates.find(template => template(p) match {
      case None => false
      case other =>
        matched = other; true
    })
    matched
  }  

  // TODO: make special case to exclude iterators here?
  /**
   * @return true if there are constraints on two or more fields of the same object in @param constraints,
   * and returns a thunk that adds the set of fields that we think may be an invariant to a failed set
   * this thunk should be called after a failed piecewise jump
   */
  def objectInvariantTemplate(p : Path) : Option[(Path, Qry => Boolean, Any => Unit)] = {
    val q = p.qry.clone
    val varConstraintMap = q.heapConstraints.foldLeft (Map.empty[ObjVar,Set[IField]]) ((m, e) => e match {
      case ObjPtEdge(lhs@ObjVar(_), InstanceFld(fld), _) => Util.updateSMap(m, lhs, fld) 
      case _ => m
    })
    // TODO: consider multiple matches instead of just the first one?
    varConstraintMap.find(pair => pair._2.size > 1 && !failedObjInvariants.contains(pair._2)) match {
      case Some((objVar, flds)) =>
        // TODO: extract this to a method and use in other templates too?
        // if we have a constraint x.f -> o where o != null and pt(x.f) is a singleton set, we're not very likely to
        // find a refutation by jumping to writes of x.f (in fact, we'll only find a refutation if the assignment is
        // x.f = null. instead, drop such constraints and keep ones we're likely to find refutations with
        val singletonPointsToConstraints = q.heapConstraints.filter(e => e match {
          case ObjPtEdge(ObjVar(srcRgn), InstanceFld(fld), ObjVar(snkRgn)) =>
            snkRgn.size == 1 && flds.contains(fld) && PtUtil.getPtI(srcRgn, fld, tf.hg).size == 1
          case _ => false
        })

        if (singletonPointsToConstraints.size >= 2) None // we would need to drop too much; give up
        else {
          // weaken heapPath so it only contains constraints containing the fields involved in the invariants
          q.dropConstraintsNotContaining(objVar, flds)
          singletonPointsToConstraints.foreach(c => {
            if (DEBUG) println(s"Dropping constraint $c due to singleton points-to set")
            q.removeHeapConstraint(c)
          })
          // another less aggressive choice: keep the o.f -> _, o.g -> _ constraints and anything reachable from them
          //q.dropConstraintsNotReachableFrom(q.heapConstraints.filter(e => e.src == objVar).toSet)

          // we consider the invariant produced if none of the constraints have any of the relevant fields anymore
          val producedInvariantCallback: Qry => Boolean = ((q: Qry) => {
            !q.heapConstraints.exists(e => e.fld match {
              case InstanceFld(fld) => flds.contains(fld)
              case _ => false
            })
          })

          val failureCallback: Any => Unit = ((x: Any) => failedObjInvariants.add(flds))
          if (DEBUG) println(s"Matched object invariant template; found constraints on more than one fld of var $objVar flds: $flds")
          Some(p.deepCopy(q), producedInvariantCallback, failureCallback)
        }
      case None => None
    }      
  }
  
  //private val failedClinits = Util.makeSet[MSet[HeapPtEdge]] // TODO: use MinPathSet here?
  private val neverProducedCallback : Qry => Boolean = ((q : Qry) => false) 
  
  def contextSensitiveTemplate(p : Path) : Option[(Path, Qry => Boolean, Any => Unit)] = {
    def tryWriteConstraintsAsLinearSequence() = {
      p.qry.constraintsAsLinearSequence match {
        case Some(seq) => // can write *all* constraints as x -> A, A.f -> B, B.g -> C, ...
          if (DEBUG) println("Matched context-sensitive template!")
          val q = p.qry.clone
          q.dropConstraintsNotReachableFrom(Set(seq.last)) // drop all constraints but the last in the sequence
          Some((p.deepCopy(q), neverProducedCallback, (_ : Any) => ()))
        case None => None
      }
    }

    val localConstraints = p.qry.localConstraints
    if (p.qry.heapConstraints.size > 1 && localConstraints.size <= 1) {
      if (localConstraints.isEmpty) tryWriteConstraintsAsLinearSequence()
      else localConstraints.head.snk match {
        case PureVar(_) => None
        case ObjVar(_) => tryWriteConstraintsAsLinearSequence()
      }
    } else None
  }
  
  /*
  // TODO: this is too aggressive. should have to be all clinits and parameters
  def classInitTemplate(p : Path) : Option[(Path, Qry => Boolean, Any => Unit)] = { 
    val heapConstraints = p.qry.heapConstraints
    if (!heapConstraints.isEmpty && !failedClinits.contains(heapConstraints) &&
        //constraints.exists(c => c.isClinitConstraint()) &&
        //constraints.forall(c => c.isClinitConstraint() || c.getVars().forall(v => !v.isLocalVar() || v.isParameter()))) {
        // TODO: check locals constraints too?
        heapConstraints.forall(e => e.isClinitEdge)) {
      println("Matched class init template " + p.qry)
      val failureCallback : Any => Unit = ((x : Any) => failedClinits.add(heapConstraints))
      // we consider class init constraints to never be produced, since nothing can be produced before them!
      Some(p.deepCopy, neverProducedCallback, failureCallback) // TODO: add callback here?
    } else None 
  }*/
  
}