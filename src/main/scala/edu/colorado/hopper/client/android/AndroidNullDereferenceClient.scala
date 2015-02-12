package edu.colorado.hopper.client.android

import java.io.File

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.classLoader.{IMethod, IField, IClass}
import com.ibm.wala.demandpa.alg.BudgetExceededException
import com.ibm.wala.ipa.callgraph.impl.FakeRootClass
import com.ibm.wala.ipa.callgraph.{CallGraph, CGNode}
import com.ibm.wala.ipa.callgraph.propagation._
import com.ibm.wala.ipa.modref.ModRef
import com.ibm.wala.ssa._
import com.ibm.wala.util.graph.traverse.BFSIterator
import edu.colorado.droidel.constants.{AndroidConstants, AndroidLifecycle, DroidelConstants}
import edu.colorado.droidel.driver.AbsurdityIdentifier
import edu.colorado.hopper.client.{ClientTests, NullDereferenceTransferFunctions}
import edu.colorado.hopper.executor.DefaultSymbolicExecutor
import edu.colorado.hopper.jumping.{ControlFeasibilityRelevanceRelation, RelevanceRelation, DefaultJumpingSymbolicExecutor, JumpingTransferFunctions}
import edu.colorado.hopper.solver.Z3Solver
import edu.colorado.hopper.state._
import edu.colorado.hopper.util.PtUtil
import edu.colorado.thresher.core.Options
import edu.colorado.walautil.Types.MSet
import edu.colorado.walautil._
import AndroidNullDereferenceClient._

import scala.collection.JavaConversions._
import scala.sys.process._

import scala.xml.XML

object AndroidNullDereferenceClient {

  // special reachability check to account for call graph imprecision in Android apps. the problem is that whenever a
  // method that places a message on the event queue is reachable, this starts a thread that calls dispatchMessage()
  // and then can pull *any* message off of the event queue (and thus call pretty much anything). we prevent this from
  // happening by cutting off paths that pass through Handler.dispatchMessage()
  def getReachableInAndroidCG(cg : CallGraph, n : CGNode) : Set[CGNode] = {
    val HANDLER_CLASS = "Landroid/os/Handler"
    val DISPATCH_MESSAGE = "dispatchMessage"
    def frontierFilter(n : CGNode) : Boolean = {
      val m = n.getMethod
      m.getDeclaringClass.getName.toString == HANDLER_CLASS && m.getName.toString == DISPATCH_MESSAGE
    }
    val iter =
      new BFSIterator[CGNode](cg, n) {
        override def getConnected(n : CGNode) : java.util.Iterator[_ <: CGNode] =
          cg.getSuccNodes(n).filter(n => frontierFilter(n))
      }
    GraphUtil.bfsIterFold(iter, Set.empty[CGNode], ((s : Set[CGNode], n : CGNode) => s + n))
  }
}

class AndroidNullDereferenceClient(appPath : String, androidLib : File, useJPhantom : Boolean = true)
    extends DroidelClient(appPath, androidLib, useJPhantom) {

  val DEBUG = Options.SCALA_DEBUG
  val rr =
    if (Options.JUMPING_EXECUTION)
      if (Options.CONTROL_FEASIBILITY)
        new ControlFeasibilityRelevanceRelation(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha) {

          val callbackClasses =
            appTransformer.getCallbackClasses().foldLeft (Set.empty[IClass]) ((s, t) => cha.lookupClass(t) match {
              case null => s
              case c =>
                val subs = cha.computeSubClasses(t).foldLeft (s + c) ((s, sub) => s + sub)
                cha.getImplementors(t).foldLeft (subs) ((s, impl) => s + impl)
            })

          // TODO: this is a hack. would be better to make a complete list. at the very least, make sure we have one
          // register method for each callback type. on the other hand, we only lose precision (not soundness) by having
          // a partial list here
          val callbackRegisterMethods : Set[IMethod] =
            cg.foldLeft (Set.empty[IMethod]) ((s, n) => {
              val m = n.getMethod
              val paramTypes = ClassUtil.getParameterTypes(m)
              if (paramTypes.size == 2) {
                cha.lookupClass(paramTypes.toList(1)) match {
                  case null => s
                  case secondArg =>
                    if (appTransformer.isCallbackClass(secondArg)) s + m
                    else s
                }
              } else s
            })

          def isAndroidLifecycleType(c : IClass) : Boolean =
            AndroidLifecycle.getOrCreateFrameworkCreatedClasses(cha).exists(androidClass =>
              cha.isAssignableFrom(c, androidClass)
            )

          override def isCallableFrom(snk : CGNode, src : CGNode, cg : CallGraph) : Boolean =
            getReachableInAndroidCG(cg, src).contains(snk)

          def isFrameworkTypeOnCreate(m : IMethod) : Boolean = m.getName.toString == "onCreate" && {
            val declClass = m.getDeclaringClass
            AndroidLifecycle.getOrCreateFrameworkCreatedClasses(cha).exists(frameworkClass =>
              cha.isAssignableFrom(frameworkClass, declClass) && {
                val typeStr = ClassUtil.deWalaifyClassName(frameworkClass)
                val selectorStr = m.getReference.getSelector.toString
                AndroidLifecycle.frameworkCbMap.exists(entry => entry._1 == typeStr &&
                                                                entry._2.exists(cb => cb == selectorStr))
              }
            )
          }

          // careful: we have to look at the IR to make sure this is called unconditionally as well as looking at the call graph
          /* @return true if when we walking backward from @param callee, we hit a node satisfying @param pred on all
           * paths wtihout hitting a node satisfying @param stopPred first */
          // we have to be careful with this: need to look at the IR via isOnlyCalledFrom to be sure that callee is
          // called unconditionally
          def isOnlyCalledFrom(callee : CGNode, pred : (CGNode => Boolean),
                               stopPred : (CGNode => Boolean)) : Boolean = {

            @annotation.tailrec
            def isOnlyCalledFromRec(worklist : List[(CGNode,CGNode)], seen : Set[(CGNode, CGNode)]) : Boolean =
                worklist match {
                case Nil => true
                case (callee, caller) :: worklist =>
                  if (stopPred(caller)) false
                  else if (mustBeCalledFrom(callee, caller))
                    if (pred(caller)) isOnlyCalledFromRec(worklist, seen)
                    else {
                      val (newWorklist, newSeen) =
                        cg.getPredNodes(caller).foldLeft(worklist, seen)((pair, n) => {
                          val (worklist, seen) = pair
                          val calleeCallerPair = (caller, n)
                          if (!seen.contains(calleeCallerPair)) (calleeCallerPair :: worklist, seen + calleeCallerPair)
                          else pair
                        })
                      isOnlyCalledFromRec(newWorklist, newSeen)
                    }
                  else false
            }

            val predecessors = cg.getPredNodes(callee).toList.map(caller => (callee, caller))
            isOnlyCalledFromRec(predecessors, predecessors.toSet)
          }

          private def stopAtLibraryBoundary(n : CGNode) = ClassUtil.isLibrary(n)

          def isOnlyCalledFromConstructor(callee : CGNode) : Boolean = {
            val calleeMethod = callee.getMethod
            def isConstructor(n : CGNode) = {
              val m = n.getMethod
              m.isInit && methodsOnSameClass(m, calleeMethod)
            }
            isOnlyCalledFrom(callee, isConstructor, stopAtLibraryBoundary)
          }

          def isOnlyCalledFromOnCreate(callee : CGNode) : Boolean = {
            val calleeMethod = callee.getMethod
            def isOnCreate(n : CGNode) = {
              val m = n.getMethod
              isFrameworkTypeOnCreate(m) && methodsOnSameClass(m, calleeMethod)
            }
            isOnlyCalledFrom(callee, isOnCreate, stopAtLibraryBoundary)
          }

          def extendsOrImplementsCallbackClass(c : IClass) : Boolean = callbackClasses.contains(c)

          def isCallbackRegisterMethod(m : IMethod) : Boolean = callbackRegisterMethods.contains(m)

          def getNodesThatMayRegisterCb(cb : PointerKey) : Set[CGNode] =
            hg.getSuccNodes(cb).foldLeft(Set.empty[CGNode])((s, k) =>
              hg.getPredNodes(k).foldLeft(s)((s, k) => k match {
                case l: LocalPointerKey =>
                  val n = l.getNode
                  if (isCallbackRegisterMethod(n.getMethod)) s + n
                  else s
                case _ => s
              })
            )

          // TODO: can be smarter here--reason about overides and calls to super
          def methodsOnSameClass(m1 : IMethod, m2 : IMethod) =
            !m1.isSynthetic && !m2.isSynthetic &&
            (m1.getDeclaringClass == m2.getDeclaringClass || m2.getDeclaringClass.getAllMethods.contains(m1))

          // TODO: restructure this to avoid redundant computation
          def androidSpecificMustHappenBefore(n1 : CGNode, n2 : CGNode, checked : Set[(CGNode, CGNode)]) : Boolean =
            if (checked.contains((n1, n2))) false
            else (n1.getMethod, n2.getMethod) match {
              case (m1, m2) if m1.isInit && methodsOnSameClass(m1, m2) && isFrameworkTypeOnCreate(m2) =>
                true // <init> always happens before onCreate
              case (m1, m2) if methodsOnSameClass(m1, m2) && isOnlyCalledFromConstructor(n1) &&
                               (isFrameworkTypeOnCreate(m2) || isOnlyCalledFromOnCreate(n2)) =>
                true // similar to previous case, but for methods always called only from <init>
              case (m1, m2) if !m2.isInit && methodsOnSameClass(m1, m2) && isFrameworkTypeOnCreate(m1) &&
                               !m1.getDeclaringClass.getDeclaredMethods.exists(m =>
                                 m.isInit && cg.getNodes(m.getReference).exists(n => isCallableFrom(n2, n, cg))) =>
                true // C.onCreate() gets called before any method C.m() that is not called from a constructor
              case (m1, m2) if !m2.isInit && methodsOnSameClass(m1, m2) && isOnlyCalledFromOnCreate(n1) =>
                true // similar to previous case, but for methods called only from onCreate()
              case (m1, m2) if extendsOrImplementsCallbackClass(m2.getDeclaringClass) =>
                // find methods M_reg where m2 may be registered. happens-before constraints that hold on (m1, m_reg)
                // for *all* m_reg in M-reg also hold for (m1, m2).
                // find callback registration methods whose parameters may be bound to this callback object
                val cbObj = hm.getPointerKeyForLocal(n2, IRUtil.thisVar)
                val nodesThatMayRegisterCb = getNodesThatMayRegisterCb(cbObj)
                // find application-scope methods that call the cb register method
                val cbRegisterCallers =
                  nodesThatMayRegisterCb.foldLeft (Set.empty[CGNode]) ((s, n) =>
                    cg.getPredNodes(n).foldLeft (s) ((s, n) => if (!ClassUtil.isLibrary(n)) s + n else s)
                  )
                // if n1 must happen before all methods that register the callback, then the n1 must happen before the
                // callback is invoked
                if (cbRegisterCallers.isEmpty) false
                else {
                  val (res, _) =
                    cbRegisterCallers.foldLeft(false, checked)((pair, caller) => {
                      val (res, checked) = pair
                      if (res || caller == n1) pair
                      else {
                        val newChecked = checked + ((n1, n2))
                        if (caller != n2 && !isCallableFrom(caller, n1, cg)) {
                          (mustHappenBefore(n1, caller, newChecked), newChecked)
                        } else (res, newChecked)
                      }
                    })
                  res
                }
              // TODO: Application.onCreate() gets called before any other lifecycle methods
              case _ => false
          }

          override def mustHappenBefore(n1 : CGNode, n2 : CGNode,
                                        checked : Set[(CGNode, CGNode)] = Set.empty) : Boolean = {
            if (DEBUG) println(s"Determining if ${ClassUtil.pretty(n1)} < ${ClassUtil.pretty(n2)}")
            super.mustHappenBefore(n1, n2, checked) || androidSpecificMustHappenBefore(n1, n2, checked)
          }
        }

      else new RelevanceRelation(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)
    else null

  val tf = new NullDereferenceTransferFunctions(walaRes, new File(s"$appPath/nit_annots.xml")) {

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

    // TODO: always add null constraints? add if we have >= 1 field in our query?
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
                                     modRef : java.util.Map[CGNode,com.ibm.wala.util.intset.OrdinalSet[PointerKey]],
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

  val exec =
    if (Options.JUMPING_EXECUTION) new DefaultJumpingSymbolicExecutor(tf, rr) {

      // TODO: do we want this?
      override val keepLoopConstraints = true

      private def doJump(p : Path) : Iterable[Path] = {
        p.qry.localConstraints.clear()
        if (DEBUG) println("After weakening, query is " + p.qry)
        val curJmp = { jmpNum += 1; jmpNum }
        rr.getPiecewisePaths(p, curJmp) match {
          case Some(unfilteredPiecewisePaths) =>
            val piecewisePaths =
              unfilteredPiecewisePaths.filter(p => !piecewiseInvMap.pathEntailsInv((p.node, p.blk, p.index), p))
            if (DEBUG) {
              println(s"got ${piecewisePaths.size} piecewise paths:")
              piecewisePaths.foreach(p => print(s"\n${p.id}X : ${ClassUtil.pretty(p.node)}\n$p")); println
            }
            piecewisePaths
          case None => super.returnFromCall(p)
        }
      }

      // TODO: if callee is relevant to heap constraint only, choose to jump instead of diving in?
      override def returnFromCall(p : Path) : Iterable[Path] =
        if (p.callStackSize == 1) {
          val qry = p.qry
          // keep one constraint on null and the access path to the constraint--drop all other constraints
          qry.heapConstraints.find(e => e.snk match {
            case p@PureVar(t) if t.isReferenceType => qry.isNull(p)
            case _ => false
          }) match {
            case Some(e) =>
              val keepEdges = qry.getAccessPrefixPathFor(e)
              // guaranteed to exist because getAccessPathPrefix returns at least e
              val accessPathHead = keepEdges.head.src
              // see if the access path leading to the null constraint is rooted in a function parameter other than
              // "this". if this is the case, we want to keep going backward without jumping in order to get a more
              // complete access path to the null constraint
              val accessPathRootedInNonThisParam =
                qry.localConstraints.exists(e => e match {
                  case LocalPtEdge(LocalVar(key), snk) =>
                    snk == accessPathHead && !IRUtil.isThisVar(key.getValueNumber)
                  case _ => false
                })
              // have access path originating from non-this param and not at an entrypoint callback, don't jump
              if (accessPathRootedInNonThisParam && !isEntrypointCallback(p.node)) super.returnFromCall(p)
              else { // have access path originating from this or at entrypoint callback, jump
                // TODO: remove inner class this constraints?
                if (DEBUG) println(s"have complete access path or at function boundary of entrypoint cb ${p.node}")
                // weaken query by removing all constraints but access path, then jump
                qry.heapConstraints.foreach(e => if (!keepEdges.contains(e)) qry.removeHeapConstraint(e))
                doJump(p)
              }
            case None =>
              // keep entire query
              if (isEntrypointCallback(p.node)) { // at function of entrypoint callback--we should jump
                if (DEBUG) println(s"at function boundary of entrypoint cb ${p.node}")
                doJump(p)
              } else super.returnFromCall(p)
          }
        } else super.returnFromCall(p)

      override def forkToPredecessorBlocks(instrPaths : List[Path], startBlk : ISSABasicBlock,
                                           loopHeader : Option[ISSABasicBlock], ir : IR, passPaths : List[Path],
                                           failPaths : List[Path], test : Path => Boolean) =
        super.forkToPredecessorBlocksNoJump(instrPaths, startBlk, loopHeader, ir, passPaths, failPaths, test)

      override def shouldJump(p : Path) : Option[(Path, Qry => Boolean, Unit => Any)] =
        Some((p.deepCopy, ((q : Qry) => true), Util.NOP))

      override def handleEmptyCallees(paths : List[Path], i : SSAInvokeInstruction, caller : CGNode) : List[Path] =
        handleEmptyCalleesImpl(paths, i, caller, tf.hm)

    } else new DefaultSymbolicExecutor(tf) {
      override def handleEmptyCallees(paths : List[Path], i : SSAInvokeInstruction, caller : CGNode) : List[Path] =
        handleEmptyCalleesImpl(paths, i, caller, tf.hm)
    }

  val solver = new Z3Solver

  /* @return true if @param i can perform a null dereference */
  def canDerefFail(i : SSAInstruction, n : CGNode, hm : HeapModel, count : Int) = {
    val ir = n.getIR()
    val tbl = ir.getSymbolTable
    val srcLine = IRUtil.getSourceLine(i, ir)
    if (Options.LINE == -2 || Options.LINE == srcLine) {
      print(s"Checking possible null deref #$count ")
      ClassUtil.pp_instr(i, ir);
      println(s" at source line $srcLine of ${ClassUtil.pretty(n)}")
      val possiblyNullUse = i.getUse(0)
      if (tbl.isNullConstant(possiblyNullUse)) {
        // have null.foo() or null.f = ... or x = null.f
        // technically, this can still be safe if the code is unreachable or protected by a try block, but philosophically
        // this is useless code and ought to be reported as on error
        println("Found definite null deref!")
        true
      } else {
        // create the query
        val lpk = Var.makeLPK(possiblyNullUse, n, hm)
        val nullPure = Pure.makePureVar(lpk)
        val locEdge = PtEdge.make(lpk, nullPure)
        val qry = Qry.make(List(locEdge), i, n, hm, solver, startBeforeI = true)
        qry.addPureConstraint(Pure.makeEqNullConstraint(nullPure))
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
        exec.cleanup()
        print(s"Deref #$count ")
        ClassUtil.pp_instr(i, ir)
        println(s" at source line $srcLine of ${ClassUtil.pretty(n)} can fail? $foundWitness")
        foundWitness
      }
    } else {
      println(s"Skipping check at source line $srcLine of ${ClassUtil.pretty(n)}")
      true
    }
  }

  def isEntrypointCallback(n : CGNode) : Boolean =
    !ClassUtil.isLibrary(n) && walaRes.cg.getPredNodes(n).exists(n => ClassUtil.isLibrary(n))

  def checkNullDerefs() : (Int,Int) = {
    import walaRes._
    /*val id = new AbsurdityIdentifier("")
    val absurdities = id.getAbsurdities(walaRes, reportLibraryAbsurdities = false)
    println(s"Have ${absurdities.size} absurdities")*/

    def shouldCheck(n : CGNode) : Boolean = {
      // TODO: tmp, just for testing
      val checkClass = if (Options.MAIN_CLASS == "Main") true else n.getMethod.getDeclaringClass.getName.toString.contains(Options.MAIN_CLASS)
      val checkMethod = if (Options.MAIN_METHOD == "main") true else n.getMethod.getName.toString == Options.MAIN_METHOD
      checkClass && checkMethod && !ClassUtil.isLibrary(n)
    }

    val (nullDerefs, derefsChecked) =
      walaRes.cg.foldLeft (0,0) ((countPair, n) => {
        if (shouldCheck(n)) n.getIR match {
          case null => countPair
          case ir =>
            val tbl = ir.getSymbolTable
            ir.getInstructions.foldLeft (countPair) ((countPair, i) => {
              val (failCount, totalCount) = countPair
              i match {
                case i: SSAInvokeInstruction if !i.isStatic && !IRUtil.isThisVar(i.getReceiver) &&
                  !i.getDeclaredTarget.isInit && !tbl.isStringConstant(i.getReceiver) =>
                  if (canDerefFail(i, n, walaRes.hm, totalCount)) (failCount + 1, totalCount + 1)
                  else (failCount, totalCount + 1)
                case i: SSAFieldAccessInstruction if !i.isStatic && !IRUtil.isThisVar(i.getRef) =>
                  if (canDerefFail(i, n, walaRes.hm, totalCount)) (failCount + 1, totalCount + 1)
                  else (failCount, totalCount + 1)

                case _ => countPair
              }
            })
        } else countPair
      })

    println(s"Found $nullDerefs potential null derefs out of $derefsChecked derefs checked")
    (nullDerefs, derefsChecked)
  }
}

object AndroidNullDereferenceClientTests extends ClientTests {

  override def runRegressionTests() : Unit = {
    val tests =
      List("InitRefute", "InitNoRefute", "OnCreateRefute", "OnCreateNoRefute", "CbRefute", "CbNoRefute",
           "OnCreateCalleeRefute", "OnCreateCalleeNoRefute")

    val regressionDir = "src/test/java/nulls/"
    val regressionBinDir = "target/scala-2.10/test-classes/nulls"
    val classesPathPrefix = s"$regressionDir/bin"
    val classesPath = s"$classesPathPrefix/classes"
    if (new File(classesPathPrefix).exists()) Process(Seq("rm", "-r", classesPathPrefix)).!!
    Process(Seq("mkdir", "-p", classesPath)).!!
    Process(Seq("cp", "-r", regressionBinDir, classesPath)).!!

    if (!(new File(Options.DROIDEL_HOME).exists())) Options.DROIDEL_HOME = "lib/droidel"
    val androidJar = new File(s"${Options.DROIDEL_HOME}/stubs/out/droidel_android-4.4.2_r1.jar")
    assert(androidJar.exists(), s"Android jar ${androidJar.getAbsolutePath} does not exist")

    Options.JUMPING_EXECUTION = true
    Options.CONTROL_FEASIBILITY = true
    val client = new AndroidNullDereferenceClient(appPath = regressionDir, androidLib = androidJar, useJPhantom = false)
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