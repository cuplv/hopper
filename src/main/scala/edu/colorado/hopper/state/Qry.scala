package edu.colorado.hopper.state

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.classLoader.IField
import com.ibm.wala.ipa.callgraph.propagation.{HeapModel, InstanceKey}
import com.ibm.wala.ipa.callgraph.{CGNode, ContextKey}
import com.ibm.wala.ssa.{ISSABasicBlock, SSAInstruction}
import edu.colorado.hopper.solver.{Solver, UnknownSMTResult, Z3Solver}
import edu.colorado.hopper.state.Qry._
import edu.colorado.walautil.{CFGUtil, Util, IRUtil}
import edu.colorado.walautil.Types.MSet
import edu.colorado.hopper.util.PtUtil
import edu.colorado.thresher.core.Options

object Qry {
  private def DEBUG = Options.SCALA_DEBUG  
  private var qryIdCounter = 0
  private def getFreshQryId = { qryIdCounter += 1; qryIdCounter }
  
  val NULL = Pure.makePureObjVar
  def getNullVar(q : Qry) : PureVar = {
    q.addPureConstraint(Pure.makeEqNullConstraint(NULL))
    NULL
  }
  
  def getStartLoc(i : SSAInstruction, n : CGNode) : (ISSABasicBlock,Int) = CFGUtil.findInstr(n, i) match {
    case Some(pair) => pair
    case None => sys.error("Couldn't find instruction " + i + " in IR for " + n)
  }
  
  def constraintsToString(s : MSet[_], sep : String) : String = Util.toCSVStr(s, sep) 
  
  /** start execution at the beginning of @param n */
  def make(startEdges : Iterable[PtEdge], n : CGNode,  hm : HeapModel) : Qry = {
    val (localConstraints, heapConstraints) = makeLocalAndHeapConstraints(startEdges, n, hm)
    val callStack = makeCallStack(n, localConstraints, n.getIR().getControlFlowGraph().entry(), -1)
    new Qry(heapConstraints, Util.makeSet[PureConstraint], callStack, new Z3Solver)
  }
  
  /** @param startBeforeI - if false, @param i will be the first instruction processed; otherwise, @param i will not be processed */
  def make(startEdges : Iterable[PtEdge], i : SSAInstruction, n : CGNode, hm : HeapModel, startBeforeI : Boolean = false) : Qry = {
    val (startBlk, startLine) = getStartLoc(i, n)
    val (localConstraints, heapConstraints) = makeLocalAndHeapConstraints(startEdges, n, hm)
    if (DEBUG) localConstraints.foldLeft (Set.empty[StackVar]) ((s, e) => { assert(!s.contains(e.src), e.src + " appears as LHS more than once in " + localConstraints); s + e.src })
    val callStack = makeCallStack(n, localConstraints, startBlk, if (startBeforeI) startLine - 1 else startLine)
    // TODO: add options to use solvers other than Z3
    new Qry(heapConstraints, Util.makeSet[PureConstraint], callStack, new Z3Solver)
  } 
  
  private def makeCallStack(n : CGNode, localConstraints : MSet[LocalPtEdge], startBlk : ISSABasicBlock, startLine : Int) : CallStack = {
    val frame = new CallStackFrame(n, localConstraints, startBlk, startLine)
    val callStack = new CallStack
    callStack.push(frame)
    callStack
  }


  // TODO: add support for converting other kinds of contextual constraints
  /** convert contextual constraints from @param n into LocalPtEdge's that Thresher understands */
  private def getContextualConstraints(n : CGNode, localConstraints : MSet[LocalPtEdge],
                                       hm : HeapModel) : List[LocalPtEdge] = {
    val ctx = n.getContext()
    val RECEIVER_VALUE_NUM = 1

    ctx.get(ContextKey.RECEIVER) match {
      case i : InstanceKey =>
        val receiverLHS = Var.makeLocalVar(RECEIVER_VALUE_NUM, n, hm)
        localConstraints.find(e => e.src == receiverLHS) match {
          case Some(e) => List(e)
          case None => List(PtEdge.make(receiverLHS, ObjVar(Set(i))))
        }
      case _ => Nil
    }
  }
  
  private def makeLocalAndHeapConstraints(startEdges : Iterable[PtEdge], n : CGNode,
                                          hm : HeapModel) : (MSet[LocalPtEdge],MSet[HeapPtEdge]) = {
    val localConstraints = Util.makeSet[LocalPtEdge]
    val heapConstraints = Util.makeSet[HeapPtEdge]
    startEdges.foreach(e => e match {
      case e : LocalPtEdge => localConstraints += e        
      case e : HeapPtEdge => heapConstraints += e      
    })
    localConstraints ++= getContextualConstraints(n, localConstraints, hm)
    (localConstraints, heapConstraints)
  }
  
  def getPT[K,V](v : K, constraints : Iterable[PtEdge]) : Set[V] = 
    constraints.foldLeft (Set.empty[V]) ((set, e) => if (e.src == v) set + e.snk.asInstanceOf[V] else set)     
  
  // TODO: combine
  private def heapImplies(l1 : MSet[HeapPtEdge], l2 : MSet[HeapPtEdge]) : Boolean = {
    l1.size >= l2.size && {
      // for every edge in l2, there exists some edge in l1 with a smaller concretization
      l2.forall(e1 => l1.exists(e2 => e1 |= e2))
      //l2.forall(e1 => l1.contains(e1) || l1.exists(e2 => e1 |= e2))
    }
  }
  
  // check l1 |= l2
  private def |=(l1 : MSet[LocalPtEdge], l2 : MSet[LocalPtEdge]) : Boolean = {
    l1.size >= l2.size && {
      // for every edge in l2, there exists some edge in l1 with a smaller concretization
      l2.forall(e1 => l1.exists(e2 => e1 |= e2))
      //l2.forall(e1 => l1.contains(e1) || l1.exists(e2 => e1 |= e2))
    }
  }
  
  def indicesPossiblyEqual(qry : Qry, fld : ArrayFld, indexVar : PureVar) : Boolean = fld.index match {
    case Some(index) =>
      try
        qry.checkTmpPureConstraint(Pure.makeEqConstraint(indexVar, index))
      catch {
        case e : UnknownSMTResult => true
      }
    case None => true // no index specified; could be equal
  }          
  
  def indicesDefinitelyEqual(qry : Qry, fld : ArrayFld, indexVar : PureVar) : Boolean = fld.index match {
    case Some(index) =>
      try
        !qry.checkTmpPureConstraint(Pure.makeNeConstraint(indexVar, index))
      catch {
        case e : UnknownSMTResult => false
      }
    case None => false // no index specified; might not be equal
  }  
}

/** mutable query holding all analysis state. program loc information (including current method and current line number) is stored in the callStack field */
class Qry(val heapConstraints : MSet[HeapPtEdge], val pureConstraints : MSet[PureConstraint], val callStack : CallStack, private val solver : Solver[_],
          val parents : List[Int] = List.empty[Int], val id : Int = getFreshQryId) extends Concretizable {
        
  private val assumes = (id :: parents).map(i => i.toString)
  def localConstraints : MSet[LocalPtEdge] = callStack.top.localConstraints
  def node : CGNode = callStack.top.node
  def blk : ISSABasicBlock = callStack.top.blk
  def index : Int = callStack.top.index
    
  def curInstr : Option[SSAInstruction] = callStack.top.curInstr
  // warning: expensive
  def curSourceLine : Int = curInstr match {
    case Some(instr) => IRUtil.getSourceLine(instr, node.getIR())
    case None => -1
  }
  
  def hasConstraint : Boolean = !heapConstraints.isEmpty || !localConstraints.isEmpty
  def constraints : Iterator[PtEdge] = localConstraints.iterator ++ heapConstraints.iterator
    
  def addLocalConstraint(e : LocalPtEdge) : Unit = {
    if (DEBUG) { 
      e.src match {
        case LocalVar(key) =>
          val ir = key.getNode().getIR()
          val tbl = ir.getSymbolTable()
          assert(!tbl.isConstant(key.getValueNumber()), s"Trying to add const edge $e IR $ir")
        case ReturnVar(key) => () 
      }
      assert(!localConstraints.exists(edg => edg.src == e.src && edg.snk != e.snk),
             s"Trying to add duplicate edge $e $localConstraints")
    }
    localConstraints += e
  }
  // TODO: is it even necessary to remove local constraints? they just go away when we pop the call stack
  def removeLocalConstraint(e : LocalPtEdge) : Unit = {
    require(localConstraints.contains(e), "Qry does not have local constraint " + e + " " + this)
    //println("removing local constraint " + e + " to " + id)
    localConstraints -= e
  }
  
  def removePureConstraint(p : PureConstraint) : Unit = pureConstraints -= p
  
  def addHeapConstraint(e : HeapPtEdge) : Boolean = if (heapConstraints.contains(e)) true else {
    
    def simultaneousPointsToError : Boolean = {
      if (DEBUG) println("e is " + e + " heap constraints are " + heapConstraints)
      if (Options.PRINT_REFS) println(s"Refuted by simultaneous points-to on field ${e.fld}")
      false 
    }
    
    val sameSrcAndField = heapConstraints.filter(_e => e.src == _e.src && e.fld ==_e.fld && !e.fld.isInstanceOf[ArrayFld])
    if (sameSrcAndField.isEmpty) {
      heapConstraints += e
      true
    } else e.snk match {
      case newSnk@PureVar(_) =>
        sameSrcAndField.forall(e => e.snk match {
          case p@PureVar(_) =>
            // found simultaneous pts-to, but the RHS's are pure vals
            // just add an equality constraint between them
            val res = addPureConstraint(Pure.makeEqConstraint(newSnk, p))
            res
          case _ => simultaneousPointsToError     
        })
      case _ => simultaneousPointsToError
    }   
  }
  
  def removeHeapConstraint(e : HeapPtEdge) : Unit = {
    require(heapConstraints.contains(e), "Qry does not have heap constraint " + e + " " + this)
    //println("Removing heap constraint " + e + " to " + id)
    heapConstraints -= e
  }
  
  def removeConstraint(e : PtEdge) = e match {
    case e : HeapPtEdge => removeHeapConstraint(e)
    case e : LocalPtEdge => removeLocalConstraint(e)
  }
  
  /** @return a set of *all* ObjVar's referenced by the query, including ones referenced by local constraints on the call stack*/
  def getAllObjVars : Set[ObjVar] = {
    def keepObjVars(l1 : MSet[_ <: PtEdge], l2 : Set[ObjVar]) : Set[ObjVar] =
      l1.foldLeft (l2) ((l,e) => e.getVals.foldLeft (l) ((l, v) => v match {
      case v@ObjVar(_) => l + v
      case _ => l      
    })) 
    val localObjVars = callStack.stack.foldLeft (Set.empty[ObjVar]) ((s, f) => keepObjVars(f.localConstraints, s))
    keepObjVars(heapConstraints, localObjVars)
  }

  private def isDefinitelyBool(p : PureVar, bool : Boolean) = {
    try {
      !qry.checkTmpPureConstraint(Pure.makeEqBoolConstraint(p, !bool))
    } catch {
      case e : UnknownSMTResult => false
    }
  }

  /** @return true if @param p is definitely false, false otherwise */
  def isDefinitelyTrue(p : PureVar) : Boolean = isDefinitelyBool(p, true)

  /** @return true if @param p is definitely true, false otherwise */
  def isDefinitelyFalse(p : PureVar) : Boolean = isDefinitelyBool(p, false)

  /** @return true if @param p is definitely null, false otherwise */
  def isNull(p : PureVar) : Boolean = {
    require(p.isReferenceType, "Expected reference type for PureVar p")
    // p is null if the solver says UNSAT to a neq null constraint
    try {
      !checkTmpPureConstraint(Pure.makeNeNullConstraint(p))
    } catch {
      case e : UnknownSMTResult => false
    }
    /*
    pureConstraints.find(c => c.lhs == p) match {
      case Some(c) => c.rhs match {
        case BoolVal(b) => 
          //if (c.isEqualityConstraint) !b else b
          val res1 = if (c.isEqualityConstraint) !b else b
          assert(res0 == res1, "disagreement! res0 " + res0 + " qry " + qry)
          res1          
        case _ => sys.error("Bad rhs for reference type " + c.rhs)
      }
      case None => sys.error("No related constraints for " + p)
    }*/
  }
    
  def addPureConstraint(p : PureConstraint) : Boolean = {
    if (p.isStringConstraint) p match {
      case PureAtomicConstraint(p@PureVar(_), _, _) => 
        // TODO: string constraints unsupported for now. just add != null constraint
        val neqNullConstraint = Pure.makeNeNullConstraint(p)         
        if (pureConstraints.add(neqNullConstraint)) solver.mkAssertWithAssumption(id.toString, neqNullConstraint)          
      case p => sys.error("Unexpected pure atomic constraint " + p)
    } else if (p.isBitwiseConstraint || p.isFloatConstraint || p.isLongConstraint) p match {
      case PureAtomicConstraint(p@PureVar(_), _, _) => 
        // TODO: bitvector, long, and float ops unsuppored for now. drop related constraints
        localConstraints.foreach(e => if (e.snk == p) localConstraints.remove(e))
        heapConstraints.foreach(e => if (e.snk == p) heapConstraints.remove(e))       
      case p => sys.error("Unexpected pure atomic constraint " + p)
    } else { // normal case      
       // TODO: do substitution in equality case?
      // add constraint id => p
      if (pureConstraints.add(p)) solver.mkAssertWithAssumption(id.toString, p)         
    }   

    try {
      val res = checkPureConstraintsSAT
      if (!res && Options.PRINT_REFS) println(s"Refuted by pure constraint! ${this.id}")
      res
    } catch {
      case e : UnknownSMTResult =>
        // SMT solver can't handle this constraint; just drop it and assume SAT
        removePureConstraint(p)
        true
    }
  }  
  
  // "assumptions" here are the id's of the current query and each of its parent queries. whenever a query adds a pure constraint p, it adds "id => p"
  //def checkPureConstraintsSAT : Boolean = solver.checkSATWithAssumptions(assumes)
  
  def checkPureConstraintsSAT : Boolean = {    
    val res = solver.checkSATWithAssumptions(assumes)
    //if (!res) println(solver.getUNSATCore)
    res
  }

  // add tmpConstraint, check SAT, (implicitly) remove tmp constraint, return result of SAT check
  def checkTmpPureConstraint(tmpConstraint : PureConstraint) : Boolean = {
    //val tmpConstraintId = getFreshTmpConstraintId
    //solver.mkAssertWithAssumption(tmpConstraintId, tmpConstraint) 
    //val res0 = solver.checkSATWithAssumptions(tmpConstraintId.toString :: assumes)
    // TODO: assert !tmpConstraintId?
    solver.checkTemporaryConstraint(tmpConstraint, assumes)
    //assert(res0 == res1)
    //res0
  }
  
  //def getRelatedPureConstraints(p : PureVar) : MSet[PureConstraint] = pureConstraints.filter(c => c.lhs == p || c.rhs == p)
  
  def intersectAndSubstitute(o1 : ObjVar, rgn : Set[InstanceKey], hg : HeapGraph[InstanceKey]) : Option[ObjVar] =
    intersectAndSubstitute(o1, ObjVar(rgn), hg, subO2 = false)
  
  def intersectAndSubstitute(o1 : ObjVar, o2 : ObjVar, hg : HeapGraph[InstanceKey],
                             subO2 : Boolean = true) : Option[ObjVar] =
    if (o1 == o2) Some(o1)
    else if (Var.canAlias(o1, o2)) {
      val rgnInter = o1.rgn.intersect(o2.rgn)
      if (rgnInter.isEmpty) {
        if (Options.PRINT_REFS) println("Refuted by from constraints!")
        None
      } else {
        // TODO: try this optimization if (toSub.rgn.size == subFor.rgn.size) true
        val interVar = ObjVar(rgnInter)
        interVar.cantAlias ++= o1.cantAlias
        if (subO2) interVar.cantAlias ++= o2.cantAlias
        if (substitute(interVar, o1, hg) && (!subO2 || substitute(interVar, o2, hg))) Some(interVar)
        else None
      }
    } else {
      if (Options.PRINT_REFS) println("Refuted by non-aliasing constraints!")
      None
    }
  /** substitute symbolic object @param toSub for symbolic object @param subFor in our constraints*/
  def substitute(toSub : ObjVar, subFor : ObjVar, hg : HeapGraph[InstanceKey]) : Boolean = {
    
    def substituteInternal(subMap : Map[ObjVar,ObjVar]) : Boolean = {
      def substituteLocals(localConstraints : MSet[LocalPtEdge]) =
        localConstraints.foreach(edge => edge.snk match {
          case o@ObjVar(_) => if (subMap.contains(o)) {
            localConstraints -= edge
            localConstraints += LocalPtEdge(edge.src, subMap(o))
          }
        case _ => ()
      })

      callStack.stack.foreach(f => substituteLocals(f.localConstraints))
           
      heapConstraints.foreach(edge => {  
        val srcMatch = edge.src.isInstanceOf[ObjVar] && subMap.contains(edge.src.asInstanceOf[ObjVar])
        val snkMatch = edge.snk.isInstanceOf[ObjVar] && subMap.contains(edge.snk.asInstanceOf[ObjVar])
        if (srcMatch || snkMatch) {
          val newSrc = if (srcMatch) subMap(edge.src.asInstanceOf[ObjVar]) else edge.src
          val newSnk = if (snkMatch) subMap(edge.snk.asInstanceOf[ObjVar]) else edge.snk
          
          
          
          removeHeapConstraint(edge)
          if (!addHeapConstraint(PtEdge.make(newSrc, edge.fld, newSnk))) return false
        }      
      })
      true
    }
    
    if (Options.AGGRESSIVE_FROM_NARROWING) {      
      // take newRgn = ptRgn \cap constraintObj and update m(constraintObj) = newRgn \cap m(constraintObj)
      def updateObjRgnMap(ptRgn : Set[InstanceKey], constraintObj : ObjVar, m : Map[ObjVar,Set[InstanceKey]]) = {
        val newRgn = ptRgn.intersect(constraintObj.rgn)
        if (newRgn.size < constraintObj.rgn.size || newRgn.size < ptRgn.size) m + (constraintObj -> m.getOrElse(constraintObj, newRgn).intersect(newRgn))
        else m // didn't get any narrowing
      }        
      
      //val objRgnMap = heapConstraints.foldLeft (Map.empty[ObjVar,Set[InstanceKey]]) ((m, e) => {
      val objRgnMap = heapConstraints.foldLeft (Map(subFor -> toSub.rgn.intersect(subFor.rgn))) ((m, e) => {
        val (srcMatch, snkMatch) = (e.src == subFor, e.snk == subFor)
        //assert (!(srcMatch && snkMatch), "src and snk of " + e + " both match " + subFor)
        val newM = if (srcMatch) e.snk match {
          case snk@ObjVar(_) =>
           //println("src match")
            e.fld match {
              case InstanceFld(fld) =>
               // println("ptO  " + toSub + "." + fld + " is " +  PtUtil.getPtO(toSub, fld, heapConstraints, hg)._1)
                //println("snk is " + snk)
                updateObjRgnMap(PtUtil.getPtO(toSub, fld, heapConstraints, hg)._1.rgn, snk, m)
              case ArrayFld(_, _, _) => updateObjRgnMap(PtUtil.getPtA(toSub, hg), snk, m)
              case _ => sys.error("unreachable")
            }
          case _ => m
        } else m
        
        if (snkMatch) e.src match {
          case src@ObjVar(_) =>
            //println("snk match")
            e.fld match {
              case InstanceFld(fld) =>
                updateObjRgnMap(PtUtil.getPtByFld(toSub.rgn, fld, hg), src, newM)
              case ArrayFld(keys, _, _) =>
                updateObjRgnMap(PtUtil.getPtByArr(toSub.rgn, hg), src, newM)
                //assert(!PtUtil.getPtByArr(toSub.rgn, hg).intersect(toSub.rgn).isEmpty, 
                   // "rgn " + PtUtil.getPtByArr(toSub.rgn, hg) + " and " + toSub + " lead to empty!") 
                //newM
              case _ => sys.error("unreachable")
            }
          case _ => newM
        } else newM
      })
      //assert(!objRgnMap.contains(toSub), toSub + " in map")
      //assert(!objRgnMap.contains(subFor), subFor + " in map")
      if (objRgnMap.values.exists(k => k.isEmpty)) {
        //sys.error("got ref! " + objRgnMap)
        if (Options.PRINT_REFS) println("Refuted by from constraint simplification!")
        return false
      }
      objRgnMap.keys.foreach(k => assert(!objRgnMap(k).isEmpty, "refuted by " + k))
      // map of subFor -> toSub
      //val subMap = objRgnMap.map(p => (ObjVar(p._2) -> p._1)) + (subFor -> toSub)       
      val subMap = objRgnMap.map(p => (ObjVar(p._2) -> p._1))
      substituteInternal(subMap)
    } else substituteInternal(Map(subFor -> toSub))
   
  /*
    heapConstraints.foreach(edge => {  
      val (srcMatch, snkMatch) = (edge.src == subFor, edge.snk == subFor)
      if (srcMatch || snkMatch) {
        val newSrc = if (srcMatch) toSub else edge.src
        val newSnk = if (snkMatch) toSub else edge.snk
        removeHeapConstraint(edge)
        addHeapConstraint(PtEdge.make(newSrc, edge.fld, newSnk))
      }     
    })*/
    
    //if (DEBUG) doObjVarSanityCheck(toSub)
  }  
  
  // drop constraints that are not of the form o.f -> _ for f in flds
  def dropConstraintsNotContaining(o : ObjVar, flds : Set[IField]) : Unit = heapConstraints.foreach(e => e match {
    case ObjPtEdge(lhs@ObjVar(_), InstanceFld(fld), _) if o == lhs && flds.contains(fld) => () // keep it 
    case _ => removeHeapConstraint(e) // drop it
  })
  
  def dropConstraintsNotReachableFrom(keepEdges : Set[HeapPtEdge]) : Unit = {
    if (DEBUG) require(keepEdges.subsetOf(heapConstraints))
    
    dropConstraintsNotReachableFrom(keepEdges.foldLeft (Set.empty[ObjVar]) ((s, e) => e.snk match {
      case o@ObjVar(_) => s + o
      case _ => s
    }), keepEdges)
  }
  
  // drop all constraints that are not in keepEdges or reachable from a constraint in keepEdges
  def dropConstraintsNotReachableFrom(keepVars : Set[ObjVar], keepEdges : Set[HeapPtEdge] = Set.empty) : Unit = {
        
    @annotation.tailrec
    def getConstraintsNotReachableFromRec(keepVars : Set[ObjVar], keepEdges : Set[HeapPtEdge]) : Set[HeapPtEdge] = {
      val (newEdges, newVars) = heapConstraints.foldLeft (keepEdges, keepVars) ((pair, e) => {
        val (keepEdges, keepVars) = pair
        e.src match {
          case src@ObjVar(_) if (keepVars.contains(src)) => e.snk match {
            case o@ObjVar(_) => (keepEdges + e, keepVars + o)
            case _ => (keepEdges + e, keepVars)
          }
          case _ => pair
        }       
      })
      if (newVars.size == keepVars.size) newEdges
      else getConstraintsNotReachableFromRec(newVars, newEdges)
    }    
    // find reachable constraints and drop all others
    val allKeepEdges = getConstraintsNotReachableFromRec(keepVars, keepEdges)
    heapConstraints.foreach(e => if (!allKeepEdges.contains(e)) this.heapConstraints.remove(e))
  }
  
  // @return if we can view *all* the local and heap constraints as a linear sequence A.f -> B, B.g -> C, etc., return the sequence of heap constraints
  def constraintsAsLinearSequence : Option[List[HeapPtEdge]] = {
    @annotation.tailrec
    def buildSequenceRec(matchVar: ObjVar, matchedList: List[HeapPtEdge]): Option[List[HeapPtEdge]] =
      if (matchedList.size == this.heapConstraints.size) Some(matchedList.reverse)
      else heapConstraints.find(e => e.src == matchVar) match {
        case Some(e@ObjPtEdge(_, _, snk@ObjVar(_))) => buildSequenceRec(snk, e :: matchedList)
        case Some(e@ArrayPtEdge(_, _, snk@ObjVar(_))) => buildSequenceRec(snk, e :: matchedList)
        case _ => None
      }

    if (this.localConstraints.size == 1 && this.heapConstraints.size >= 1) localConstraints.head.snk match {
      case snk@ObjVar(_) =>
        buildSequenceRec(snk, Nil)
      case _ => None
    } else if (localConstraints.isEmpty && this.heapConstraints.size >= 1)
      this.heapConstraints.foldLeft(None: Option[List[HeapPtEdge]])((l, e) =>
        if (l.isDefined) l
        else e.snk match {
          case o@ObjVar(_) => buildSequenceRec(o, List(e))
          case _ => None
        }
      )
    else None
  }
   
  /*
  // TODO: this name is dumb
  // @return true if we can view *all* the local and heap constraints as a linear sequence A.f -> B, B.g -> C, etc.   
  def allConstraintsFormLinearSequence : Boolean = this.localConstraints.size == 1 && this.heapConstraints.size >= 1 && {       
    localConstraints.head.snk match {
      case snk : HeapVar =>
        def buildSequenceRec(matchVar : HeapVar, matchedCount : Int) : Boolean = matchedCount == this.heapConstraints.size || {
          heapConstraints.find(e => e.src == matchVar) match {
            case Some(ObjPtEdge(_, _, snk : HeapVar)) => buildSequenceRec(snk, matchedCount + 1)
            case Some(ArrayPtEdge(_, _, snk : HeapVar)) => buildSequenceRec(snk, matchedCount + 1)
            case _ => false
          }
        }        
        buildSequenceRec(snk, 0)
      case _ => false
    }    
  }*/
  
  // debug only
  def doFullObjVarSanityCheck() : Unit = getAllObjVars.foreach(v => doObjVarSanityCheck(v))
  
  def doObjVarSanityCheck(v : ObjVar) = {
    if (v.rgn.size == 1) {
        heapConstraints.foreach(e => e match {
          case ObjPtEdge(o1@ObjVar(rgn1), _, o2@ObjVar(rgn2)) =>
            if (rgn1.size == 1 && rgn1 == v.rgn) assert(o1 == v, "Mismatched vars " + o1 + " and " + v)
            if (rgn2.size == 1 && rgn2 == v.rgn) assert(o2 == v, "Mismatched vars " + o2 + " and " + v)
          case _ => ()
        })
      }
  }
  
  def foundWitness : Boolean = localConstraints.isEmpty && {
    try
     checkPureConstraintsSAT
    catch {
      case e : UnknownSMTResult => true // conservatively assume SAT
    }
  }
  
  def getPT(v : StackVar) : Set[Val] = Qry.getPT(v, localConstraints)
  
  def dispose() : Unit = solver.dispose
  
  def cleanup() : Unit = dispose
  
  override def |=(other : Concretizable) : Boolean = other match {
    case q : Qry => Qry.heapImplies(this.heapConstraints, q.heapConstraints) && //q.heapConstraints.forall(c => this.heapConstraints.contains(c)) &&
                    // TODO: implement |= for call stack and delegate
                    q.callStack.size == this.callStack.size &&
                    q.node == this.node &&
                    Qry.|=(this.localConstraints, q.localConstraints) &&
                    this.doZ3ImplicationCheck(q)
    case _ => sys.error("comparing qry to " + other)
  }
  
  private def doZ3ImplicationCheck(q1 : Qry) : Boolean = { // TODO: refactor to use existing context
    // temporary context for performing implication checking
    //final Z3Context tmp = new Z3Context(new Z3Config());
    solver.push
    solver.mkNotImpliesAssert(pureConstraints, q1.pureConstraints)
    //solver.mkAssert(solver.mkNot(solver.mkImplies(pureConstraints, q1.pureConstraints))
    //val (implLHS, implRHS) = (solver.toConjunct(pureConstraints), solver.toConjunct(q1.pureConstraints))
    //solver.mkAssert(solver.mkNot(solver.mkImplies(implLHS, implRHS)))
    val res = !solver.checkSAT
    solver.pop
    res
  }  
  
  override def deepCopy : Concretizable = sys.error("no")
  
  override def qry = this
  
  override def toString : String = id + "Q { " + constraintsToString(localConstraints, " *\n") + " *\n" + constraintsToString(heapConstraints, " *\n") + 
    " }\n{( " + constraintsToString(pureConstraints, " ^\n") + " )}"   
  //override def toString : String = id + " { " + constraintsToString(localConstraints) + " *\n" + constraintsToString(heapConstraints) + " }"
  //override def toString : String = "{ " + localConstraints + heapConstraints + " }\n{( " + pureConstraints + " )}"   
      
  override def clone : Qry = new Qry(heapConstraints.clone, pureConstraints.clone, callStack.clone, solver, id :: parents)
  
  /*
  override def clone : Qry = {
    this.poison
    new Qry(heapConstraints.clone, pureConstraints.clone, callStack.clone, solver, id :: parents)  
  }
  
  var isPoisoned : Boolean = false
  
  def poison : Unit = {
    println("poisoning " + id)
    Thread.dumpStack()
    isPoisoned = true
  }*/
  
  override def hashCode : Int = Util.makeHash(List(heapConstraints, pureConstraints, callStack))
  
  override def equals(other : Any) : Boolean = other match {
    case q : Qry => this.heapConstraints == q.heapConstraints  &&
                    this.pureConstraints == q.pureConstraints && // TODO: ask Z3 about these?                  
                    this.callStack == q.callStack // TODO: is this too restrictive?
    case _ => false
  }
  
  /*
  override def equals(other : Any) : Boolean = other match {
    case q : Qry =>
      println("this stack " + this.callStack.size + " and " + q.callStack.size)
      println("comparing " + this + " and " + q)
      println("heapEq? " + (this.heapConstraints == q.heapConstraints))
      println("pureEq? " + (this.pureConstraints == q.pureConstraints))
      println("call stk equal? " + (this.callStack == q.callStack))
      this.heapConstraints == q.heapConstraints  &&
                    this.pureConstraints == q.pureConstraints && // TODO: ask Z3 about these?                  
                    this.callStack == q.callStack // TODO: is this too restrictive?
    case _ => false
  }*/
}
