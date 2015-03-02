package edu.colorado.hopper.client.android

import java.io.File
import java.util

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.classLoader.{IBytecodeMethod, IMethod, IField, IClass}
import com.ibm.wala.demandpa.alg.BudgetExceededException
import com.ibm.wala.ipa.callgraph.impl.{Everywhere, FakeRootClass}
import com.ibm.wala.ipa.callgraph.{CallGraph, CGNode}
import com.ibm.wala.ipa.callgraph.propagation._
import com.ibm.wala.ipa.modref.ModRef
import com.ibm.wala.ssa._
import com.ibm.wala.types._
import com.ibm.wala.util.graph.dominators.Dominators
import com.ibm.wala.util.graph.impl.{GraphInverter, DelegatingNumberedNodeManager}
import com.ibm.wala.util.graph.{Graph, NumberedEdgeManager, AbstractNumberedGraph, NumberedGraph}
import com.ibm.wala.util.graph.traverse.BFSIterator
import com.ibm.wala.util.intset.IntSet
import edu.colorado.droidel.constants.{AndroidConstants, AndroidLifecycle, DroidelConstants}
import edu.colorado.droidel.constants.AndroidLifecycle._
import edu.colorado.droidel.driver.AbsurdityIdentifier
import edu.colorado.hopper.client.{ClientTests, NullDereferenceTransferFunctions}
import edu.colorado.hopper.executor.{TransferFunctions, DefaultSymbolicExecutor}
import edu.colorado.hopper.jumping.{ControlFeasibilityRelevanceRelation, RelevanceRelation, DefaultJumpingSymbolicExecutor, JumpingTransferFunctions}
import edu.colorado.hopper.solver.{Z3Solver, ThreadSafeZ3Solver}
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

          val activityLifecycleGraph = AndroidLifecycle.makeActivityLifecycleGraph(cha)
          val serviceLifecycleGraph = AndroidLifecycle.makeServiceLifecycleGraph(cha)
          val appFragmentLifecycleGraph =
            AndroidLifecycle.makeFragmentLifecycleGraph(TypeName.findOrCreate(ClassUtil.walaifyClassName(AndroidConstants.APP_FRAGMENT_TYPE)), cha)
          val supportFragmentLifecycleGraph =
            AndroidLifecycle.makeFragmentLifecycleGraph(TypeName.findOrCreate(ClassUtil.walaifyClassName(AndroidConstants.FRAGMENT_TYPE)), cha)

          def isAndroidLifecycleType(c : IClass) : Boolean =
            AndroidLifecycle.getOrCreateFrameworkCreatedClasses(cha).exists(androidClass =>
              cha.isAssignableFrom(androidClass, c)
            )

          def isFrameworkOrStubNode(n : CGNode) : Boolean =
            ClassUtil.isLibrary(n) || {
              val methodName = n.getMethod.getDeclaringClass.getName.toString
              methodName.startsWith(s"L${DroidelConstants.STUB_DIR}") ||
              methodName.startsWith(s"L${DroidelConstants.HARNESS_DIR}") ||
              methodName.startsWith(s"L${DroidelConstants.PREWRITTEN_STUB_DIR}")
            }

          /** given an application-space CGNode n, compute the node(s) invoked by the framework that may call this node.
            * to be more concrete, if the app is onCreate() { foo() } onDestroy() { foo() } and n is foo, then this
            * method will return {onCreate, onDestroy} */
          def getLibraryAppFrontierNodesFor(n : CGNode) : Set[CGNode] = {
            // library nodes are already on the wrong side of the library/app frontier, can't do anything
            if (isFrameworkOrStubNode(n)) Set(n)
            else {
              val iter = new BFSIterator[CGNode](cg, n) {
                override def getConnected(n: CGNode): java.util.Iterator[_ <: CGNode] = {
                  cg.getPredNodes(n).filter(n => !isFrameworkOrStubNode(n))
                }
              }

              def hasNonAppPred(n: CGNode): Boolean = cg.getPredNodes(n).exists(n => isFrameworkOrStubNode(n))

              val initFrontierNodes = if (hasNonAppPred(n)) Set(n) else Set.empty[CGNode]
              GraphUtil.bfsIterFold(iter, initFrontierNodes, ((s: Set[CGNode], n: CGNode) =>
                if (hasNonAppPred(n)) s + n
                else s
              ))
            }
          }

          def specializeLifecycleGraph(curNode : CGNode, relevantMethods : Set[IMethod]) : GraphImpl[IMethod] = {
            if (DEBUG) println(s"Doing lifecycle specialization for ${ClassUtil.pretty(curNode)}")
            val curMethod = curNode.getMethod
            val curClass = curMethod.getDeclaringClass
            val curNodeIsCallback = extendsOrImplementsCallbackClass(curClass)
            val (lifecycleClass, frontierMethodsForRegister) =
              if (curNodeIsCallback && !isAndroidLifecycleType(curClass)) {
                val cbObj = hm.getPointerKeyForLocal(curNode, IRUtil.thisVar)
                val nodesThatMayRegisterCb = getNodesThatMayRegisterCb(cbObj)
                // get the frontier nodes that (transitively) call the registration method
                val frontierMethodsForRegister =
                  nodesThatMayRegisterCb.foldLeft (Set.empty[IMethod]) ((s, n) => {
                    val registerPreds = cg.getPredNodes(n)
                    registerPreds.foldLeft (s) ((s, n) =>
                      if (!ClassUtil.isLibrary(n))
                        getLibraryAppFrontierNodesFor(n).foldLeft(s)((s, n) => s + n.getMethod)
                      else s
                    )
                  })
                if (frontierMethodsForRegister.isEmpty) (curClass, Set.empty[IMethod])
                else
                  // pick the class of the register method of the lifecycle we care with
                  (frontierMethodsForRegister.head.getDeclaringClass, frontierMethodsForRegister)
              } else (curClass, Set.empty[IMethod])
            if (DEBUG) println(s"Picked lifecycle class ${ClassUtil.pretty(lifecycleClass)}")

            // start off with the standard Java lifecycle graph--<clinit> -> constructor for all constructros
            val clinit = lifecycleClass.getClassInitializer match {
              case null =>
                cg.getFakeRootNode.getMethod // no class initializer, but we need a single root. make something up
              case clinit => clinit
            }
            val specializedLifecyleGraph = new GraphImpl[IMethod](root = Some(clinit))
            val constructors = lifecycleClass.getDeclaredMethods.filter(m => m.isInit)
            // add <clinit> -> constructor happens-before edges
            constructors.foreach(constructor => specializedLifecyleGraph.addEdge(clinit, constructor))

            def specializeAndroidLifecycleGraph(lifecycleGraph : GraphImpl[IMethod]) : Unit = {
              // if methods contains a method m such that c.originalMethod() resolves to m, return m. else, return
              // originalMethod
              def trySpecializeMethod(originalMethod : IMethod, methods : Set[IMethod],
                                      c : IClass) : Option[IMethod] = {
                val classRef = c.getReference
                val resolvedMethod =
                  cha.resolveMethod(MethodReference.findOrCreate(classRef, originalMethod.getSelector))
                if (methods.contains(resolvedMethod)) Some(resolvedMethod)
                else None
              }

              // try to specialize methods in the lifecycle graph template to methods in our class of interest
              val specializationMap =
                lifecycleGraph.nodes.foldLeft (Map.empty[IMethod,IMethod]) ((m, method) => {
                  trySpecializeMethod(method, relevantMethods, lifecycleClass) match {
                    case Some(specializedMethod) => m + (method -> specializedMethod)
                    case None => m
                  }
                })

              lifecycleGraph.root match {
                case Some(root) =>
                  val newRoot = specializationMap.getOrElse(root, root)
                  // add contructor -> root edges
                  constructors.foreach(constructor => specializedLifecyleGraph.addEdge(constructor, newRoot))
                case None => sys.error("expecting rooted graph")
              }

              // walk through the lifecycle graph and add its edges to our specialized graph, using the specialization
              // map as appropriate
              lifecycleGraph.edges.foreach(edgePair => {
                val (src, snk) = edgePair
                val (newSrc, newSnk) = (specializationMap.getOrElse(src, src), specializationMap.getOrElse(snk, snk))
                specializedLifecyleGraph.addEdge(newSrc, newSnk)
              })
            }

            val ACTIVITY_TYPE_STR = ClassUtil.walaifyClassName(AndroidConstants.ACTIVITY_TYPE)
            val SERVICE_TYPE_STR = ClassUtil.walaifyClassName(AndroidConstants.SERVICE_TYPE)
            val APP_FRAGMENT_TYPE_STR = ClassUtil.walaifyClassName(AndroidConstants.APP_FRAGMENT_TYPE)
            val SUPPORT_FRAGMENT_TYPE_STR = ClassUtil.walaifyClassName(AndroidConstants.FRAGMENT_TYPE)

            // each lifecycle type has an "active" state where it processes user interactions. this method returns the
            // last method in the lifcycle graph that is called before the type enters the active state
            def getActiveStatePredecessor(typeStr : String, lifecycleGraph : GraphImpl[IMethod]) : Option[IMethod] =
              typeStr match {
                case ACTIVITY_TYPE_STR =>
                  lifecycleGraph.nodes().find(m =>
                    m.getSelector == Selector.make(AndroidLifecycle.ACTIVITY_ONPREPAREOPTIONSMENU))
                case SERVICE_TYPE_STR =>
                  lifecycleGraph.nodes().find(m => m.getSelector == Selector.make(AndroidLifecycle.SERVICE_ONCREATE))
                case APP_FRAGMENT_TYPE_STR =>
                  lifecycleGraph.nodes().find(m => m.getSelector == Selector.make(AndroidLifecycle.FRAGMENT_ONRESUME))
                case SUPPORT_FRAGMENT_TYPE_STR =>
                  lifecycleGraph.nodes().find(m => m.getSelector == Selector.make(AndroidLifecycle.FRAGMENT_ONRESUME))
                case _ => None
            }

            // check if c extends an Android framework type. if it does, we'll create a specialized lifecycle graph for
            // it. if it doesn't, we'll just give it the standard Java lifecycle graph
            AndroidLifecycle.getOrCreateFrameworkCreatedClasses(cha).find(frameworkClass =>
              cha.isAssignableFrom(frameworkClass, lifecycleClass)) match {
                case Some(frameworkClass) =>
                  // got Android lifecycle type
                  val typeStr =frameworkClass.getReference.getName.toString
                  typeStr match {
                    case ACTIVITY_TYPE_STR => specializeAndroidLifecycleGraph (activityLifecycleGraph)
                    case SERVICE_TYPE_STR => specializeAndroidLifecycleGraph (serviceLifecycleGraph)
                    case APP_FRAGMENT_TYPE_STR => specializeAndroidLifecycleGraph (appFragmentLifecycleGraph)
                    case SUPPORT_FRAGMENT_TYPE_STR => specializeAndroidLifecycleGraph (supportFragmentLifecycleGraph)
                    case _ => // else. we don't know anything about the lifecycle of this component
                  }
                  if (curNodeIsCallback && curMethod.getDeclaringClass == lifecycleClass &&
                      !specializedLifecyleGraph.nodes.contains(curMethod))
                    getActiveStatePredecessor(typeStr, specializedLifecyleGraph) match {
                      case Some(activeStatePred) =>
                        // this type has an active state. find any of its callbacks cb that are not in the lifecycle graph
                        // and add {active state} -> cb edges to account for the fact that these callbacks only fire in
                        // the active state for the component
                        specializedLifecyleGraph.addEdge(activeStatePred, curMethod)
                      case None => ()
                    }
                case None => () // got "normal" type, nothing else to do
              }

            if (curNodeIsCallback) {
              val lifecycleGraphMethods = specializedLifecyleGraph.nodes().toSet
              // add edge from register method to the callback. this models the constraint that the callback must be
              // registered somewhere before cb
              frontierMethodsForRegister.foreach(registerMethod =>
                if (lifecycleGraphMethods.contains(registerMethod))
                specializedLifecyleGraph.addEdge(registerMethod, curMethod)
              )
            }

            specializedLifecyleGraph
          }

          def controlFeasibilityFilter(nodeModMap : Map[CGNode,Set[SSAInstruction]], curNode : CGNode) = {
            val curMethod = curNode.getMethod
            val (frontierMethods, frontierToOriginalMap) =
              nodeModMap.foldLeft (Set.empty[IMethod], Map.empty[IMethod,Set[CGNode]]) ((pair, entry) => {
                val curNode = entry._1
                val frontierMethodsForCurNode = getLibraryAppFrontierNodesFor(curNode).map(n => n.getMethod)
                frontierMethodsForCurNode.foldLeft (pair) ((pair, method) => {
                  val (frontierMethods, frontierToOriginalMap) = pair
                  (frontierMethods + method, Util.updateSMap(frontierToOriginalMap, method, curNode))
                })
              })

            assert(!frontierMethods.isEmpty, "Should always have nonzero number of frontier methods")
            // create a lifecycle graph for the class of the current method
            val lifecycleGraph =
              specializeLifecycleGraph(curNode, frontierMethods + curMethod)
            if (DEBUG) {
              println("Specialized lifecycle graph:")
              lifecycleGraph.edges().foreach(p => println(s"${ClassUtil.pretty(p._1)} -> ${ClassUtil.pretty(p._2)}"))
            }
            val (methodsToVisitMustAlias, methodsToVisitMustNotAlias) = {
              val graphMethods = lifecycleGraph.nodes().toSet
              if (!graphMethods.contains(curMethod))
                // current method has no lifecycle constraints, any frontier method could be visited next
                (frontierMethods, Set.empty[IMethod])
              else {
                val (methodsInLifecycleGraph, methodsNotInLifecyleGraph) =
                  frontierMethods.partition(m => graphMethods.contains(m))
                lifecycleGraph.root match {
                  case Some(root) =>
                    val iter = new BFSIterator[IMethod](lifecycleGraph, lifecycleGraph.getPredNodes(curMethod)) {
                      override def getConnected(n: IMethod): java.util.Iterator[_ <: IMethod] = {
                        // cut off the search when we hit a relevant method
                        if (frontierMethods.contains(n)) java.util.Collections.emptyIterator()
                        else asJavaIterator(lifecycleGraph.getPredNodes(n))
                      }
                    }
                    val toVisitIfMustAlias =
                      GraphUtil.bfsIterFold(iter, methodsNotInLifecyleGraph, ((s: Set[IMethod], m: IMethod) =>
                        if (frontierMethods.contains(m)) s + m
                        else s
                        )
                      )
                    val filteredByMustAlias = methodsInLifecycleGraph.filter(m => !toVisitIfMustAlias.contains(m))
                    // we can avoid visiting the nodes in this set *if* we know that the receiver of the current node
                    // must-aliases the receiver of each node in toVisit. otherwise, we must consider visiting the
                    // these nodes as well, but we get to add a receiver must-not alias constraint.
                    // we leverage this fact by quickly checking if adding this constraint makes all of the relevant
                    // instructions non-relevant. if this is the case, we can avoid visiting the node in question
                    val toVisitIfMustNotAlias = filteredByMustAlias.filter(f => {
                      val originalNodesForFrontierMethod = frontierToOriginalMap(f)
                      originalNodesForFrontierMethod.forall(n => {
                        nodeModMap(n).forall(i => {
                          val instrRelevantIfReceiverMustNotAlias =
                            i match {
                              case i : SSAPutInstruction => i.isStatic || !IRUtil.isThisVar(i.getRef)
                              case i => true
                            }
                          if (DEBUG && instrRelevantIfReceiverMustNotAlias)
                            println(s"Instruction ${ClassUtil.pretty(n)}: $i still relevant with must-not-alias")
                          instrRelevantIfReceiverMustNotAlias
                        })
                      })
                    })
                    (toVisitIfMustAlias, toVisitIfMustNotAlias)
                  case None => sys.error("Expected rooted graph")
                }
              }
            }

            val methodNodeMap = nodeModMap.map(entry => {
              val n = entry._1
              n.getMethod -> n
            })

            def getNodesForMethods(methods : Set[IMethod]) : Set[CGNode] =
              methods.foldLeft (Set.empty[CGNode]) ((s, m) =>
                methodNodeMap.get(m) match {
                  case Some(n) => s + n
                  case None => cg.getNodes(m.getReference).foldLeft (s) ((s, n) => s + n)
                }
              )
            (getNodesForMethods(methodsToVisitMustAlias), getNodesForMethods(methodsToVisitMustNotAlias))
          }

          /** return Some(paths) if we should jump, None if we should not jump */
          override def getPiecewisePaths(p: Path, jmpNum: Int): Option[List[Path]] = {
            if (DEBUG) println("Computing relevance graph")
            if (p.qry.heapConstraints.isEmpty) None
            else {
              val qry = p.qry
              val modMap = super.getNodeModifierMap(qry, ignoreLocalConstraints = true)
              if (DEBUG) println(s"Before control-feas filtering, ${modMap.keys} are relevant")
              val (nodesToJumpToMustAlias, nodesToJumpToMustNotAlias) = controlFeasibilityFilter(modMap, qry.node)

              p.clearCallStack()

              def addReceiverConstraint(qry: Qry, jmpNode: CGNode, mustAlias: Boolean): Unit =
                if (!jmpNode.getMethod.isStatic) {
                  val thisLPK = Var.makeLPK(IRUtil.thisVar, jmpNode, hm)
                  val thisPT = PtUtil.getPt(thisLPK, hg)
                  qry.heapConstraints.find(e => e match {
                    case ObjPtEdge(src@ObjVar(srcRgn), _, _) if !srcRgn.intersect(thisPT).isEmpty =>
                      val receiverVar =
                        if (mustAlias) src // must-alias, use src
                        else {
                          // must-not-alias, create fresh var
                          val freshReceiverObjVar = ObjVar(thisPT)
                          Var.markCantAlias(freshReceiverObjVar, src)
                          freshReceiverObjVar
                        }
                      qry.addLocalConstraint(PtEdge.make(Var.makeLocalVar(IRUtil.thisVar, jmpNode, hm), receiverVar))
                      true
                    case _ => false
                  })
                }

              def setUpJumpPaths(nodesToJumpTo: Set[CGNode], mustAlias: Boolean, paths: List[Path] = Nil) =
                nodesToJumpTo.foldLeft(paths)((paths, jmpNode) => {
                  val copy = p.deepCopy
                  val jmpBlk = jmpNode.getIR.getExitBlock
                  val qry = copy.qry
                  Path.setupBlockAndCallStack(copy, jmpNode, jmpBlk, -1, jmpNum)
                  // transfer the this constraint from the current method to the jump method
                  addReceiverConstraint(qry, jmpNode, mustAlias)
                  copy :: paths
                })

              val mustAliasCases = setUpJumpPaths(nodesToJumpToMustAlias, mustAlias = true)
              Some(setUpJumpPaths(nodesToJumpToMustNotAlias, mustAlias = false, mustAliasCases))
            }
          }

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

          // careful: we have to look at the IR to make sure this is called unconditionally as well as looking at the
          // call graph
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
              // TODO: this can lead to divergence. fix
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
                      if (res || caller == n1 || checked.contains((n1, n2))) pair
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

  def makeExec() =
    if (Options.JUMPING_EXECUTION) {
      val rr = getOrCreateRelevanceRelation()
      val tf = getOrCreateTransferFunctions(rr)
      new DefaultJumpingSymbolicExecutor(tf, rr) {

      // TODO: do we want this?
      override val keepLoopConstraints = true

      private def doJump(p : Path) : Iterable[Path] = {
        require(!p.node.getMethod.isInit)
        //p.qry.localConstraints.clear()
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
                isEntrypointCallback(p.node) || {
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
              if (!shouldJump) super.returnFromCall(p)
              else { // have access path originating from this or at entrypoint callback, jump
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

      }
    } else new DefaultSymbolicExecutor(makeTF(makeRR())) {
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
        println(s"$derefId can fail? $foundWitness")
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
    println(s"Have ${absurdities.size} absurdities")
    absurdities.foreach(println)*/

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
              //val (failCount, totalCount) = countPair
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

  // this is false just to ensure this only runs once during regression tests--it is clearly jumping-compatible!
  override def isPiecewiseCompatible : Boolean = false
}