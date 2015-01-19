package edu.colorado.hopper.piecewise

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.classLoader.IMethod
import com.ibm.wala.ipa.callgraph.propagation.{HeapModel, InstanceKey}
import com.ibm.wala.ipa.callgraph.{CGNode, CallGraph}
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ssa.SSAInstruction
import com.ibm.wala.util.graph.impl.GraphInverter
import com.ibm.wala.util.graph.traverse.BFSPathFinder
import com.ibm.wala.util.intset.OrdinalSet
import edu.colorado.hopper.state.{PtEdge, Qry}
import edu.colorado.walautil.{CFGUtil, ClassUtil, IRUtil}

import scala.collection.JavaConversions._

// relevance relation that filters away instructions that are not control-feasible based on domain-specific information
// about Android
class AndroidRelevanceRelation(cg : CallGraph, hg : HeapGraph[InstanceKey], hm : HeapModel, cha : IClassHierarchy,
                               cgTransitiveClosure : java.util.Map[CGNode,OrdinalSet[CGNode]] = null)
  extends RelevanceRelation(cg, hg, hm, cha, cgTransitiveClosure) {

  val invertedCG = GraphInverter.invert(cg)

  val DEBUG = true

  override def getConstraintProducerMap(q : Qry, ignoreLocalConstraints : Boolean = false) : Map[PtEdge,List[(CGNode,SSAInstruction)]] = {
    val constraintProducerMap = super.getConstraintProducerMap(q, ignoreLocalConstraints)
    // TODO: filter!

    /*constraintProducerMap.map(pair => pair._1 match {
      case ObjPtEdge(_, InstanceFld(f), _) =>
        val fldClass = f.getReference.getDeclaringClass
        val methods = pair._2.filter(pair => pair._1.getMethod.getDeclaringClass.getReference == fldClass && // the "this" pointer is used
      case _ => pair
    })*/

    constraintProducerMap
  }


  // given current label l_cur and two relevant labels l_1 and l_2, we have two ways to rule out l_1/l_2
  // (1) l_1 and/or l_2 is not backward reachable from l_cur
  // (2) if every concrete traces visits l_1 -> l_2 -> l_cur, we can rule out l_1

  /** check condition (1); @return true if @param toFilter is not backward-reachable from @param curNode */
  def isNotBackwardReachableFrom(toFilter : CGNode, curNode : CGNode) : Boolean = {
    // TODO: implement more precise check here?
    false
  }

  def isActivityLifecycleMethod(m : IMethod) : Boolean = false

  // get the caller of @param n that is ultimately called by the Android library in order to invoke n
  // TODO: generalize to case with multiple app predecessors; too hard for now
  def getLastAppPred(n : CGNode) : Option[CGNode] = {
    cg.getPredNodes(n).filter(n => !ClassUtil.isLibrary(n)) match {
      case preds if preds.isEmpty => Some(n)
      case preds if preds.size == 1 && !preds.contains(n) => getLastAppPred(n)
      case _ => None
    }
  }

  // TODO: implement important Android lifecycle ordering facts here
  // check that method(relNode) <: method(curNode), then check that method(toFilterNode) <: method(relNode)
  def methodOrderingOk(toFilterNode : CGNode, relNode : CGNode, curNode : CGNode) : Boolean = {
    //println(s"Checking: toFilterNode: ${ClassUtil.pretty(toFilterNode)}, relNode: ${ClassUtil.pretty(relNode)}, curNode: ${ClassUtil.pretty(curNode)}")
    false
  }

  // TODO: there's some unstated precondition for being able to call this at all for the init/android-specific rules
  // (clinit rule is fine though)...something like "constraints must be fields of the
  // *same* object instance whose methods we are trying to filter, and writes to fields of that object must be through
  // the "this" pointer, or something like that". alternatively, the class whose methods are under consideration is one
  // that is somehow known or proven to have only one instance in existence at a time.

  /** @return true if we can prove that @param toFilter is control-infeasible with respect to @param curNode based on
    * the fact that @param otherRelNodes are also relevant */
  def canFilter(curNode : CGNode, toFilter : CGNode, nodeProducerMap : Map[CGNode,Set[SSAInstruction]]) : Boolean =
    isNotBackwardReachableFrom(toFilter, curNode) || {
      val path = new BFSPathFinder(cg, toFilter, curNode).find()
      // TODO: this is *very* unsound, but need to do it for now to avoid absurd paths. fix CG issues that cause this later
      // I think these CG paths happen whenever a function call places a message on the event queue--this starts a thread
      // that calls dispatchMessage() and then can pull *any* message off of the event queue. We can prevent this from
      // happening by cutting off paths that pass through Handler.dispatchMessage() (or Looper.loop())
      val reachable =
        path != null && path.size > 0 && path.exists(n => n != toFilter && n != curNode && !ClassUtil.isLibrary(n)) &&
        path.size < 20
      if (reachable) {
        println(s"can't filter $toFilter since it's reachable from ${ClassUtil.pretty(curNode)}")
        path.foreach(println)
      }

      val curMethod = curNode.getMethod
      val toFilterMethod = toFilter.getMethod
      val toFilterClass = toFilterMethod.getDeclaringClass

      // return true if i is guarded by a conditional in
      def isGuardedByConditional(i : SSAInstruction, n : CGNode) : Boolean =
        // we do the isGeneratedInstruction check because relevance adds synthetic assignments to default values when
        // needed, but these instructions don't occur in the IR (and are thus never guarded by a conditional)
        IRUtil.isGeneratedInstruction(i) ||
        !CFGUtil.isInConditionalIntraprocedural(n.getIR.getBasicBlockForInstruction(i), n.getIR.getControlFlowGraph)

      // we can filter if toFilter is a constructor o.<init>() and one of otherRelNodes is a method o.m()
      def canFilterDueToConstructor() : Boolean =
        toFilterMethod.isInit && nodeProducerMap.keys.exists(n =>
          n != toFilter && {
            val m = n.getMethod
            !m.isInit && !m.isClinit
            m.getDeclaringClass == toFilterClass
          } && nodeProducerMap(n).exists(i => isGuardedByConditional(i, n)))

      // similarly, we can filter if toFilter is a class initializer o.<clinit> and one of otherRelNodes is a method o.m()
      def canFilterDueToClassInit() : Boolean =
        toFilterMethod.isClinit && nodeProducerMap.keys.exists(n =>
          n != toFilter && n.getMethod.getDeclaringClass == toFilterClass &&
          nodeProducerMap(n).exists(i => isGuardedByConditional(i, n)))

      def canFilterBasedOnMethodOrderingInner(toFilterMethod : IMethod, relInstruction : SSAInstruction,
                                              relInstructionNode : CGNode, curMethod : IMethod) : Boolean = {
        // want to return true if toFilterMethod < relInstructionNode.getMethod < curMethod
        // TODO: allow addition of contextual constraints if caller of relInstruction method matches, but
        // relInstructionMethod doesn't match directly?
        val ir = relInstructionNode.getIR
        val cfg = ir.getControlFlowGraph
        val instrBlk =
          if (IRUtil.isGeneratedInstruction(relInstruction)) cfg.entry()
          else ir.getBasicBlockForInstruction(relInstruction)


        // TODO: make this more complicated so that it stops at the harness boundary!
        def cgNodeFilter(n : CGNode) : Boolean = true

        methodOrderingOk(toFilter, relInstructionNode, curNode) &&
        !CFGUtil.isInConditionalInterprocedural(instrBlk, relInstructionNode, cg, cgNodeFilter) &&
        !CFGUtil.isInTryBlockInterprocedural(instrBlk, relInstructionNode, cg, cgNodeFilter)
      }

      def canFilterDueToMethodOrdering(toFilterMethod : IMethod, curMethod : IMethod) : Boolean =
        nodeProducerMap.exists(pair => {
          val (relNode, relInstrs) = pair
          relInstrs.exists(relInstr =>
            canFilterBasedOnMethodOrderingInner(toFilterMethod, relInstr, relNode, curMethod))
        })

      // check if there is a path from toFilter to curNode in the call graph; if so, we can't (easily) filter, so don't try
      !reachable && {
        // TODO: what about subclassing? is there something we can do here about superclass constructors without being unsound?
        val canFilter =
          canFilterDueToConstructor() || canFilterDueToClassInit() ||
          canFilterDueToMethodOrdering(toFilterMethod, curMethod)
        // TODO: or a callee of o.m(). but this will force us to generalize the conditional check below
        // TODO: && there must be some i in n that is not guarded by a catch block locally, and n should not be guarded by a catch block in any of its callers

        // TODO: we don't actually need the check below for Android so long as we only jump at the "harness boundary", but we may need it elsewhere
        // if n (transtively) calls curNode, we don't know if it's relevant instruction will execute before curNode is
        // reached or not. we can try to figure this out, but it's rather hard so for now we just insist on unreachbility
        //!DFS.getReachableNodes(cg, java.util.Collections.singleton(n)).contains(curNode) &&
        // there must be some relevant instruction that cannot be guarded by a conditional, otherwise we cannot
        // guarantee that it will execute before we reach curNode
        // ...and there exists a relevant command in otherRelNode that must be executed on the path to the current block in curNode
        if (DEBUG && canFilter) println(s"Filtered node $toFilter!")
        canFilter
      }
    }

  override def getNodeProducerMap(q : Qry,
                                  ignoreLocalConstraints : Boolean = false) : Map[CGNode,Set[SSAInstruction]] = {
    val nodeProducerMap = super.getNodeProducerMap(q, ignoreLocalConstraints)
    nodeProducerMap.filterNot(pair => canFilter(q.node, pair._1, nodeProducerMap))
  }

}
