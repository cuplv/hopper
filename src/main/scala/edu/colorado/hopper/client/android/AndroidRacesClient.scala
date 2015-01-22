package edu.colorado.hopper.client.android

import java.io.File

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.classLoader.{IField, IClass}
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.callgraph.propagation._
import com.ibm.wala.ssa._
import edu.colorado.droidel.driver.AbsurdityIdentifier
import edu.colorado.hopper.client.NullDereferenceTransferFunctions
import edu.colorado.hopper.executor.DefaultSymbolicExecutor
import edu.colorado.hopper.piecewise.{RelevanceRelation, AndroidRelevanceRelation, DefaultPiecewiseSymbolicExecutor, PiecewiseTransferFunctions}
import edu.colorado.hopper.state._
import edu.colorado.hopper.util.PtUtil
import edu.colorado.thresher.core.Options
import edu.colorado.walautil.Types.MSet
import edu.colorado.walautil.{ClassUtil, IRUtil, Util}

import scala.collection.JavaConversions._
import scala.xml.XML

class AndroidRacesClient(appPath : String, androidLib : File) extends DroidelClient(appPath, androidLib) {
  val DEBUG = false
  lazy val rr =
    if (Options.CONTROL_FEASIBILITY) new AndroidRelevanceRelation(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)
    else new RelevanceRelation(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)

  // TODO: mixin null deref transfer functions and pw transfer functions, or otherwise allow code reuse
  lazy val tf = new NullDereferenceTransferFunctions(walaRes, new File(s"$appPath/nit_annots.xml")) {

    def useMayBeRelevantToQuery(use : Int, qry : Qry, n : CGNode, hm : HeapModel,
                                 hg : HeapGraph[InstanceKey]) : Boolean = {
      val tbl = n.getIR.getSymbolTable
      !tbl.isConstant(use) && {
        val lpk = Var.makeLPK(use, n, hm)
        qry.localConstraints.exists(e => e.src.key == lpk) || {
          val queryInstanceKeys = qry.getAllObjVars.flatMap(o => o.rgn)
          !queryInstanceKeys.intersect(PtUtil.getPt(lpk, hg)).isEmpty || qry.localMayPointIntoQuery(lpk, n, hm, hg)
        }
      }
    }

    /** @return true if we should add the conditional expression from @param cond as a constraint given that we want to
      * refute @param qry, false otherwise */
    def shouldAddConditionalConstraint(cond : SSAConditionalBranchInstruction, qry : Qry, n : CGNode) : Boolean = {
      val shouldAdd =
        useMayBeRelevantToQuery(cond.getUse(0), qry, n, hm, hg) ||
        useMayBeRelevantToQuery(cond.getUse(1), qry, n, hm, hg)
      if (DEBUG && !shouldAdd) {
        print("Not adding cond "); ClassUtil.pp_instr(cond, n.getIR); println(" since it may be irrel")
      }
      shouldAdd
    }

    override def isCallRelevant(i : SSAInvokeInstruction, caller : CGNode, callee : CGNode, qry : Qry) : Boolean =
      if (Options.PIECEWISE_EXECUTION)
        isRetvalRelevant(i, caller, qry) || PiecewiseTransferFunctions.doesCalleeModifyHeap(callee, qry, rr, cg)
      else super.isCallRelevant(i, caller, callee, qry)

    val HANDLER_CLASS = "Landroid/os/Handler"
    val DISPATCH_MESSAGE = "dispatchMessage"
    def frontierFilter(n : CGNode) : Boolean = {
      val m = n.getMethod
      m.getDeclaringClass.getName.toString == HANDLER_CLASS && m.getName.toString == DISPATCH_MESSAGE
    }

    override def dropCallConstraints(qry : Qry, callee : CGNode,
                                     modRef : java.util.Map[CGNode,com.ibm.wala.util.intset.OrdinalSet[PointerKey]],
                                     loopDrop : Boolean) : Unit =
      PiecewiseTransferFunctions.dropCallConstraints(qry, callee, rr, cg, frontierFilter)

    override def executeCond(cond : SSAConditionalBranchInstruction, qry : Qry, n : CGNode,
                             isThenBranch : Boolean) : Boolean =
      // decide whether or not we should keep the condition
      if (shouldAddConditionalConstraint(cond, qry, n)) super.executeCond(cond, qry, n, isThenBranch)
      else true
  }

  lazy val exec =
    if (Options.PIECEWISE_EXECUTION) new DefaultPiecewiseSymbolicExecutor(tf, rr) {

      // TODO: do we want this?
      override val keepLoopConstraints = true

      // TODO: if callee is relevant to heap constraint only, choose to jump instead of diving in?
      override def returnFromCall(p : Path) : Iterable[Path] =
        if (p.callStackSize == 1 && isEntrypointCallback(p.node)) {
          println(s"at function boundary of entrypoint cb ${p.node}")
          val jmpPath = p.deepCopy
          val qry = jmpPath.qry

          // drop all local constraints
          qry.localConstraints.clear()

          // keep one constraint on null and the access path to the constraint--drop all other constraints
          qry.heapConstraints.find(e => e.snk match {
            case p@PureVar(_) => qry.isNull(p)
            case _ => false
          }) match {
            case Some(e) =>
              val keepEdges = qry.getAccessPrefixPathFor(e)
              qry.heapConstraints.foreach(e => if (!keepEdges.contains(e)) qry.removeHeapConstraint(e))
            case None => () // keep entire query
          }

          if (DEBUG) println("After weakening, query is " + qry)

          if (piecewiseJumpRefuted(jmpPath)) List.empty[Path] else super.returnFromCall(p)
        } else super.returnFromCall(p)

      override def forkToPredecessorBlocks(instrPaths : List[Path], startBlk : ISSABasicBlock,
                                           loopHeader : Option[ISSABasicBlock], ir : IR, passPaths : List[Path],
                                           failPaths : List[Path], test : Path => Boolean) =
        super.forkToPredecessorBlocksNoJump(instrPaths, startBlk, loopHeader, ir, passPaths, failPaths, test)

      override def shouldJump(p : Path) : Option[(Path, Qry => Boolean, Unit => Any)] =
        Some((p.deepCopy, ((q : Qry) => true), Util.NOP))

    }
    else new DefaultSymbolicExecutor(tf)

  /* @return true if @param i can perform a null dereference */
  def canDerefFail(i : SSAInstruction, n : CGNode, hm : HeapModel, count : Int) = {
    val ir = n.getIR()
    val srcLine = IRUtil.getSourceLine(i, ir)
    print(s"Checking possible null deref #$count ")
    ClassUtil.pp_instr(i, ir); println(s" at source line $srcLine of ${ClassUtil.pretty(n)}")
    // create the query
    val lpk = Var.makeLPK(i.getUse(0), n, hm)
    val nullPure = Pure.makePureVar(lpk)
    val locEdge = PtEdge.make(lpk, nullPure)
    val qry = Qry.make(List(locEdge), i, n, hm, startBeforeI = true)
    qry.addPureConstraint(Pure.makeEqNullConstraint(nullPure))
    // invoke Thresher and check it
    val foundWitness =
      try {
        exec.executeBackward(qry)
      } catch {
        case e : Throwable =>
          println(s"Error: $e \n${e.getStackTraceString}")
          if (Options.SCALA_DEBUG) throw e
          else true // soundly assume we got a witness
      }
    print(s"Deref #$count ")
    ClassUtil.pp_instr(i, ir)
    println(s" at source line $srcLine of ${ClassUtil.pretty(n)} can fail? $foundWitness")

    foundWitness
  }

  def isEntrypointCallback(n : CGNode) : Boolean =
    !ClassUtil.isLibrary(n) && walaRes.cg.getPredNodes(n).exists(n => ClassUtil.isLibrary(n))

  def checkForRacingDerefs() = {
    import walaRes._
    /*val id = new AbsurdityIdentifier("")
    val absurdities = id.getAbsurdities(walaRes, reportLibraryAbsurdities = false)
    println(s"Have ${absurdities.size} absurdities")*/

    val callbackClasses =
      appTransformer.getCallbackClasses().foldLeft (Set.empty[IClass]) ((s, t) => cha.lookupClass(t) match {
        case null => s
        case clazz => s + clazz
      })

    // TODO: check callees of callbacks as well
    def isCallback(n : CGNode) = {
      val declClass = n.getMethod.getDeclaringClass
      callbackClasses.exists(c => cha.isSubclassOf(declClass, c) || cha.implementsInterface(declClass, c))
    }

    def shouldCheck(n : CGNode) : Boolean = {
      // TODO: tmp, just for testing
      val checkClass = if (Options.MAIN_CLASS == "Main") true else n.getMethod.getDeclaringClass.getName.toString.contains(Options.MAIN_CLASS)
      val checkMethod = if (Options.MAIN_METHOD == "main") true else n.getMethod.getName.toString == Options.MAIN_METHOD
      //println("Node is " + ClassUtil.pretty(n) + " checkClass " + checkClass + " checkMethod " + checkMethod)
      checkClass && checkMethod && !ClassUtil.isLibrary(n)
    }

    val nullDerefs =
      walaRes.cg.foldLeft (0) ((count, n) =>
        if (shouldCheck(n)) n.getIR match {
          case null => count
          case ir =>
            val tbl = ir.getSymbolTable
            ir.getInstructions.foldLeft (count) ((count, i) => i match {
              case i : SSAInvokeInstruction if !i.isStatic && !IRUtil.isThisVar(i.getReceiver) &&
                                               !i.getDeclaredTarget.isInit && !tbl.isStringConstant(i.getReceiver) =>
                if (canDerefFail(i, n, walaRes.hm, count)) count + 1
                else count

              case i : SSAFieldAccessInstruction if !i.isStatic && !IRUtil.isThisVar(i.getRef) =>
                if (canDerefFail(i, n, walaRes.hm, count)) count + 1
                else count

              case _ => count
            })
        } else count
      )

    println(s"Found $nullDerefs potential null derefs")
  }
}
