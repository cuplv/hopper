package edu.colorado.hopper.client.android

import java.io.File
import java.util

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.classLoader.IBytecodeMethod
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.callgraph.propagation._
import com.ibm.wala.ssa._
import com.ibm.wala.util.intset.OrdinalSet
import edu.colorado.droidel.driver.AbsurdityIdentifier
import edu.colorado.hopper.client.android.AndroidUtil._
import edu.colorado.hopper.client.{ClientTests, NullDereferenceTransferFunctions}
import edu.colorado.hopper.executor.DefaultSymbolicExecutor
import edu.colorado.hopper.jumping.{JumpingTransferFunctions, RelevanceRelation}
import edu.colorado.hopper.solver.{ThreadSafeZ3Solver, Z3Solver}
import edu.colorado.hopper.state._
import edu.colorado.hopper.util.PtUtil
import edu.colorado.thresher.core.Options
import edu.colorado.walautil._

import scala.collection.JavaConversions._
import scala.sys.process._

class AndroidNullDereferenceClient(appPath : String, androidLib : File, useJPhantom : Boolean = true)
    extends DroidelClient(appPath, androidLib, useJPhantom) {

  val PARALLEL = Options.PARALLEL
  val DEBUG = Options.SCALA_DEBUG

  val rr = if (PARALLEL) None else Some(makeRR())
  val tf = if (PARALLEL) None else Some(makeTF(getOrCreateRelevanceRelation()))
  val exec = if (PARALLEL) None else Some(makeExec)
  // need a single solver with synchronized methods rather than a solver per-query because the Z3 bindings are not
  // thread-safe and tend to crash even when we use multiple solvers with no shared state.
  val solver = Some(makeSolver())

  def getOrCreate[T](tOpt : Option[T], makeT : Unit => T) : T = tOpt match {
    case Some(t) => t
    case None => makeT()
  }

  def getOrCreateRelevanceRelation() = getOrCreate(rr, (_ : Unit) => makeRR)

  def getOrCreateTransferFunctions(rr : RelevanceRelation) = getOrCreate(tf, (_ : Unit) => makeTF(rr))

  def getOrCreateSymbolicExecutor() = getOrCreate(exec, (_ : Unit) => makeExec())

  def getOrCreateSolver() = getOrCreate(solver, (_ : Unit) => makeSolver())

  def makeSolver() = if (PARALLEL) new ThreadSafeZ3Solver() else new Z3Solver()

  def makeRR() : RelevanceRelation =
    if (Options.JUMPING_EXECUTION)
      if (Options.CONTROL_FEASIBILITY)
        // use control-feasibility information from Android lifecycle
        new AndroidRelevanceRelation(appTransformer, walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)
      else
        new RelevanceRelation(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)
    else null

  def makeTF(rr : RelevanceRelation) = new NullDereferenceTransferFunctions(walaRes, new File(s"$appPath/nit_annots.xml")) {

    def useMayBeRelevantToQuery(use : Int, qry : Qry, n : CGNode, hm : HeapModel,
                                hg : HeapGraph[InstanceKey]) : Boolean = {
      val tbl = n.getIR.getSymbolTable
      !tbl.isConstant(use) && {
        val lpk = Var.makeLPK(use, n, hm)
        qry.localConstraints.exists(e => e.src.key == lpk) || {
          val queryInstanceKeys = qry.getAllObjVars.flatMap(o => o.rgn)
          queryInstanceKeys.intersect(PtUtil.getPt(lpk, hg)).nonEmpty || qry.localMayPointIntoQuery(lpk, n, hm, hg, cha)
        }
      }
    }

    def isNullConstraint(cond : SSAConditionalBranchInstruction, n : CGNode) : Boolean = {
      val tbl = n.getIR.getSymbolTable
      tbl.isNullConstant(cond.getUse(0)) || tbl.isNullConstant(cond.getUse(1))
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
      if (Options.JUMPING_EXECUTION)
        isRetvalRelevant(i, caller, qry) ||
        JumpingTransferFunctions.doesCalleeModifyHeap(callee, qry, rr, cg,
                                                        getReachable = getReachableInAndroidCG)
      else super.isCallRelevant(i, caller, callee, qry)

    override def dropCallConstraints(qry : Qry, callee : CGNode,
                                     modRef : util.Map[CGNode,OrdinalSet[PointerKey]],
                                     loopDrop : Boolean) : Unit =
    if (Options.JUMPING_EXECUTION)
      JumpingTransferFunctions.dropCallConstraints(qry, callee, rr, cg,
                                                     getReachable = getReachableInAndroidCG)
    else super.dropCallConstraints(qry, callee, modRef, loopDrop)

    override def executeCond(cond : SSAConditionalBranchInstruction, qry : Qry, n : CGNode,
                             isThenBranch : Boolean) : Boolean =
      // decide whether or not we should keep the condition
      if (shouldAddConditionalConstraint(cond, qry, n)) super.executeCond(cond, qry, n, isThenBranch)
      else true
  }

  // in the case that we can't resolve a callee and we have a null constraint on the return value of the callee, refute
  // the query. this is unsound, but pragmatic: we don't want to waste time triaging unavoidable alarms due to missing
  // code
  private def handleEmptyCalleesImpl(paths : List[Path], i : SSAInvokeInstruction, caller : CGNode,
                                     hm : HeapModel) : List[Path] =
    if (i.hasDef) {
      val retval = hm.getPointerKeyForLocal(caller, i.getDef)
      paths.filter(p => !p.qry.localConstraints.exists(e => e match {
        case LocalPtEdge(LocalVar(src), pure@PureVar(t)) if retval == src && t.isReferenceType && p.qry.isNull(pure) =>
          println("Null constraint on retval of missing method, unsoundly refuting")
          true
        case e@LocalPtEdge(LocalVar(src), _) if retval == src =>
          if (DEBUG) println("No targets, dropping retval constraints")
          p.qry.removeLocalConstraint(e) // drop retval constraint
          false
        case _ => false
      }))
    } else paths

  def makeExec() =
    if (Options.JUMPING_EXECUTION) {
      val rr = getOrCreateRelevanceRelation()
      val tf = getOrCreateTransferFunctions(rr)
      new AndroidJumpingSymbolicExecutor(tf, rr) {

      override def returnFromCall(p : Path) : Iterable[Path] =
        if (p.callStackSize == 1 && !p.node.getMethod.isInit) {
          val qry = p.qry
          // keep one constraint on null and the access path to the constraint--drop all other constraints
          qry.heapConstraints.find(e => e.snk match {
            case p@PureVar(t) if t.isReferenceType => qry.isNull(p)
            case _ => false
          }) match {
            case Some(e) =>
              val keepEdges = qry.getAccessPrefixPathFor(e)
              val shouldJump =
                isEntrypointCallback(p.node, cg) || {
                  e match {
                    case ObjPtEdge(_, InstanceFld(fld), _) =>
                      val keepEdges = qry.getAccessPrefixPathFor(e)
                      // guaranteed to exist because getAccessPathPrefix returns at least e
                      val accessPathHead = keepEdges.head.src
                      // see if the access path leading to the null constraint is rooted in a function parameter other
                      // than "this". if this is the case, we want to keep going backward without jumping in order to
                      // get a more complete access path to the null constraint
                      val accessPathRootedInNonThisParam =
                        qry.localConstraints.exists(e => e match {
                          case LocalPtEdge(LocalVar(key), snk) =>
                            snk == accessPathHead && !IRUtil.isThisVar(key.getValueNumber)
                          case _ => false
                        })
                      def someCallerMayReadOrWriteFld(): Boolean = cg.getPredNodes(p.node).exists(n => n.getIR match {
                        case null => false
                        case ir =>
                          val fldRef = fld.getReference
                          ir.iterateAllInstructions().exists(i => i match {
                            case i: SSAFieldAccessInstruction => i.getDeclaredField == fldRef
                            case _ => false
                          })
                      })
                      // don't jump if the access path is not rooted in this or if a caller may read/write the field
                      // that points to nul
                      !accessPathRootedInNonThisParam && !someCallerMayReadOrWriteFld
                    case _ => false
                  }
                }
              if (!shouldJump) super.returnFromCallNoJump(p)
              else { // have access path originating from this or at entrypoint callback, jump
                if (DEBUG) println(s"have complete access path or at function boundary of entrypoint cb ${p.node}")
                // weaken query by removing all constraints but access path, then jump
                qry.heapConstraints.foreach(e => if (!keepEdges.contains(e)) qry.removeHeapConstraint(e))
                doJump(p)
              }
            case None =>
              // keep entire query
              if (isEntrypointCallback(p.node, cg)) { // at function of entrypoint callback--we should jump
                if (DEBUG) println(s"at function boundary of entrypoint cb ${p.node}")
                doJump(p)
              } else super.returnFromCallNoJump(p)
          }
        } else super.returnFromCallNoJump(p)

      override def handleEmptyCallees(paths : List[Path], i : SSAInvokeInstruction, caller : CGNode) : List[Path] =
        handleEmptyCalleesImpl(paths, i, caller, tf.hm)

      }
    } else new DefaultSymbolicExecutor(getOrCreateTransferFunctions(makeRR())) {
      override def handleEmptyCallees(paths : List[Path], i : SSAInvokeInstruction, caller : CGNode) : List[Path] =
        handleEmptyCalleesImpl(paths, i, caller, tf.hm)
    }

  /* @return true if @param i can perform a null dereference */
  def canDerefFail(instrIndex : Int, n : CGNode, hm : HeapModel, count : Int) = {
    val solver = getOrCreateSolver()
    val exec = getOrCreateSymbolicExecutor
    val i = n.getIR.getInstructions()(instrIndex)
    val ir = n.getIR()
    val tbl = ir.getSymbolTable
    val srcLine = IRUtil.getSourceLine(i, ir)
    if (Options.LINE == -2 || Options.LINE == srcLine) {
      // we need the bytecode index to differentiate different derefs at the same line
      val bytecodeIndex = n.getMethod match {
        case m : IBytecodeMethod => m.getBytecodeIndex(instrIndex)
        case _ => -1
      }

      print(s"Checking possible null deref #$count ")
      ClassUtil.pp_instr(i, ir);
      val derefId = s" at source line $srcLine bytecode index $bytecodeIndex of ${ClassUtil.pretty(n)}"
      println(derefId)
      val possiblyNullUse = i.getUse(0)
      if (tbl.isNullConstant(possiblyNullUse)) {
        // have null.foo() or null.f = ... or x = null.f
        // technically, this can still be safe if the code is unreachable or protected by a try block, but
        // philosophically this is useless code and ought to be reported as on error
        println("Found definite null deref!")
        true
      } else if (Options.FLOW_INSENSITIVE_ONLY)
        // check the derefence using the flow-insensitive non-null annotations of Nit
        exec.tf match {
          case tf : NullDereferenceTransferFunctions =>
            val cg = tf.cg
            val cha = tf.cha
            // try to find the def of possiblyNullUse and use Nit annotations to show it is assigned to a non-null value
            !ir.iterateAllInstructions().exists(i => i match {
              case i : SSAInvokeInstruction if i.getDef == possiblyNullUse =>
                // the deref cannot fail if every method this call can dispatch to has a non-null annotation
                val targets = cg.getPossibleTargets(n, i.getCallSite)
                !targets.isEmpty && targets.forall(n => tf.hasNitNonNullReturnAnnotation(n.getMethod))
              case i : SSAGetInstruction if i.getDef == possiblyNullUse =>
                // we can refute if this is a field read x = y.f and we have a non-null annotation on f
                cha.resolveField(i.getDeclaredField) match {
                  case null => false
                  case f =>
                    // the deref cannot fail if it was read from a field has a non-null annotation
                    tf.hasNitNonNullFieldAnnotation(f)
                }
              /// TODO: can add case for phi that checks all vars flowing to the phi
              case _ => false // deref'd var flows from parameter, may fail
            })
          case _ => false // transfer functions have no Nit annotations, may fail
        }
      else {
        // check the dereference using Thresher
        val lpk = Var.makeLPK(possiblyNullUse, n, hm)
        val nullPure = Pure.makePureVar(lpk)
        val locEdge = PtEdge.make(lpk, nullPure)
        val qry = Qry.make(List(locEdge), i, n, hm, solver, startBeforeI = true)
        qry.addPureConstraint(Pure.makeEqNullConstraint(nullPure))
        val qryTimer = new Timer
        qryTimer.start()
        // invoke Thresher and check it
        val foundWitness =
          try {
            exec.executeBackward(qry)
          } catch {
            case e: Throwable =>
              println(s"Error: $e \n${e.getStackTraceString}")
              if (Options.SCALA_DEBUG) throw e
              else true // soundly assume we got a witness
          }
        qryTimer.stop()
        exec.cleanup()
        print(s"Deref #$count ")
        ClassUtil.pp_instr(i, ir)
        println(s"$derefId can fail? $foundWitness. Checking took ${qryTimer.time} seconds")
        foundWitness
      }
    } else {
      println(s"Skipping check at source line $srcLine of ${ClassUtil.pretty(n)}")
      true
    }
  }

  def checkNullDerefs() : (Int,Int) = {
    import walaRes._
    if (DEBUG) {
      val id = new AbsurdityIdentifier("")
      val absurdities = id.getAbsurdities(walaRes, reportLibraryAbsurdities = false)
      println(s"Have ${absurdities.size} absurdities")
      absurdities.foreach(println)
    }

    def shouldCheck(n : CGNode) : Boolean = {
      // check Options allows us to restrict analysis to a particular class or method
      val checkClass =
        if (Options.MAIN_CLASS == "Main") true
        else n.getMethod.getDeclaringClass.getName.toString.contains(Options.MAIN_CLASS)
      val checkMethod =
        if (Options.MAIN_METHOD == "main") true else n.getMethod.getName.toString == Options.MAIN_METHOD
      checkClass && checkMethod && !ClassUtil.isLibrary(n)
    }

    val derefsToCheck =
      walaRes.cg.foldLeft (List.empty[(Int,CGNode)]) ((l, n) =>
        if (shouldCheck(n)) n.getIR match {
          case null => l
          case ir =>
            val tbl = ir.getSymbolTable
            ir.getInstructions.zipWithIndex.foldLeft(l)((l, pair) => {
              val (i, index) = pair
              i match {
                case i: SSAInvokeInstruction if !i.isStatic && !IRUtil.isThisVar(i.getReceiver) &&
                  !i.getDeclaredTarget.isInit && !tbl.isStringConstant(i.getReceiver) =>
                  (index, n) :: l
                case i: SSAFieldAccessInstruction if !i.isStatic && !IRUtil.isThisVar(i.getRef) =>
                  (index, n) :: l
                case _ => l
              }
            })
        } else l
      )

    val derefsToCheckList = if (PARALLEL) derefsToCheck.par else derefsToCheck
    val results =
      derefsToCheckList.map(pair => {
        val (index, node) = pair
        if (canDerefFail(index, node, hm, 0)) 1 else 0
      })
    val (nullDerefs, derefsChecked) = (results.sum, results.size)
    println(s"Found $nullDerefs potential null derefs out of $derefsChecked derefs checked")
    (nullDerefs, derefsChecked)
  }
}

object AndroidNullDereferenceClientTests extends ClientTests {

  override def runRegressionTests() : Unit = {
    val tests =
      List("InitRefute", "InitNoRefute", "OnCreateRefute", "OnCreateNoRefute", "CbRefute", "CbNoRefute",
           "OnCreateCalleeRefute", "OnCreateCalleeNoRefute", "DifferentInstanceNoRefute",
           "UncommonLifecycleCallbackRefute")

    if (Options.TEST == null || Options.TEST.isEmpty || tests.contains(Options.TEST)) {
      val regressionDir = "src/test/java/nulls/"
      val regressionBinDir = "target/scala-2.10/test-classes/nulls"
      val classesPathPrefix = s"$regressionDir/bin"
      val classesPath = s"$classesPathPrefix/classes"
      if (new File(classesPathPrefix).exists()) Process(Seq("rm", "-r", classesPathPrefix)).!!
      Process(Seq("mkdir", "-p", classesPath)).!!
      Process(Seq("cp", "-r", regressionBinDir, classesPath)).!!

      val androidJar = new File(Options.ANDROID_JAR)
      assert(androidJar.exists(), s"Android jar ${androidJar.getAbsolutePath} does not exist--pass a path to a valid android JAR using the -android_jar flag")

      Options.JUMPING_EXECUTION = true
      Options.CONTROL_FEASIBILITY = true
      val client =
        new AndroidNullDereferenceClient(appPath = regressionDir, androidLib = androidJar, useJPhantom = false)
      var testNum = 0
      val executionTimer = new Timer

      tests.foreach(test => if (Options.TEST == null || Options.TEST.isEmpty() || Options.TEST == test) {
        testNum += 1
        Options.MAIN_CLASS = test
        println("Running test " + testNum + ": " + test)
        val (mayFailCount, derefsChecked) = {
          try {
            executionTimer.start
            client.checkNullDerefs()
          } catch {
            case e : Throwable =>
              printTestFailureMsg(test, testNum)
              throw e
          }
        }

        executionTimer.stop
        assert(derefsChecked > 0, "Expected to check >0 derefs!")
        val mayFail = mayFailCount > 0
        // tests that we aren't meant to refute have NoRefute in name
        val expectedResult = test.contains("NoRefute")
        if (mayFail == expectedResult)
          println(s"Test $test (#$testNum) passed!")
        else {
          printTestFailureMsg(test, testNum)
          if (Options.EXIT_ON_FAIL) sys.error("Test failure")
        }

        println(s"Test took ${executionTimer.time.toInt} seconds.")
        println(s"Execution time ${executionTimer.time}")
        edu.colorado.thresher.core.WALACFGUtil.clearCaches()
        LoopUtil.clearCaches
        executionTimer.clear
      })
      Process(Seq("rm", "-r", classesPathPrefix)).!!
    }
  }

  // this is false just to ensure this only runs once during regression tests--it is clearly jumping-compatible!
  override def isPiecewiseCompatible : Boolean = false
}