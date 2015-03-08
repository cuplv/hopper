package edu.colorado.hopper.client.android

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.classLoader.{IMethod, IClass}
import com.ibm.wala.ipa.callgraph.{CGNode, CallGraph}
import com.ibm.wala.ipa.callgraph.propagation.{PointerKey, LocalPointerKey, HeapModel, InstanceKey}
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ssa.{SSAPutInstruction, SSAInstruction}
import com.ibm.wala.types.{Selector, MethodReference, TypeName}
import com.ibm.wala.util.graph.traverse.BFSIterator
import com.ibm.wala.util.intset.OrdinalSet
import edu.colorado.hopper.state._
import edu.colorado.droidel.constants.{DroidelConstants, AndroidConstants, AndroidLifecycle}
import edu.colorado.droidel.constants.AndroidConstants._
import edu.colorado.droidel.driver.AndroidAppTransformer
import edu.colorado.hopper.jumping.ControlFeasibilityRelevanceRelation
import edu.colorado.hopper.util.PtUtil
import edu.colorado.walautil._

import scala.collection.JavaConversions._

class AndroidRelevanceRelation(appTransformer : AndroidAppTransformer, cg : CallGraph, hg : HeapGraph[InstanceKey],
                               hm : HeapModel, cha : IClassHierarchy,
                               cgTransitiveClosure : java.util.Map[CGNode,OrdinalSet[CGNode]] = null)
  extends ControlFeasibilityRelevanceRelation(cg, hg, hm, cha, cgTransitiveClosure) {

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

  val activityLifecycleGraph = AndroidLifecycle.makeActivityLifecycleGraph(cha)
  val serviceLifecycleGraph = AndroidLifecycle.makeServiceLifecycleGraph(cha)
  val appFragmentLifecycleGraph =
    AndroidLifecycle.makeFragmentLifecycleGraph(TypeName.findOrCreate(ClassUtil.walaifyClassName(APP_FRAGMENT_TYPE)),
                                                cha)
  val supportFragmentLifecycleGraph =
    AndroidLifecycle.makeFragmentLifecycleGraph(TypeName.findOrCreate(ClassUtil.walaifyClassName(FRAGMENT_TYPE)), cha)

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
    if (p.qry.heapConstraints.isEmpty) None // no heap constraints, pointless to jump
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
}
