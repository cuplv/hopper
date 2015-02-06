package edu.colorado.hopper.jumping

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.ipa.callgraph.propagation.{HeapModel, InstanceKey, PointerKey}
import com.ibm.wala.ipa.callgraph.{CGNode, CallGraph}
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ssa.SSAInvokeInstruction
import com.ibm.wala.util.graph.traverse.{BFSPathFinder, DFS}
import edu.colorado.hopper.executor.TransferFunctions
import edu.colorado.hopper.executor.TransferFunctions._
import edu.colorado.hopper.jumping.JumpingTransferFunctions._
import edu.colorado.hopper.state.Qry
import edu.colorado.thresher.core.Options
import edu.colorado.walautil.{ClassUtil, GraphUtil}

import scala.collection.JavaConversions._


object JumpingTransferFunctions {
  // if true, drop constraints when a callee is relevant, but is more than Options.MAX_CALLSTACK_DEPTH steps away in the
  // call graph. this dropping will allow us to soundly report that the callee is irrelevant
  private val AGGRESSIVE_CALLEE_CONSTRAINT_DROPPING = true

  private def defaultGetReachable(cg : CallGraph, n : CGNode) : Set[CGNode] =
    DFS.getReachableNodes(cg, java.util.Collections.singleton(n)).toSet

  def doesCalleeModifyHeap(callee : CGNode, qry : Qry, rr : RelevanceRelation, cg : CallGraph,
                           getReachable : (CallGraph, CGNode) => Set[CGNode] = defaultGetReachable) : Boolean = {
    // set of nodes reachable from call at i
    val calleeReachable = getReachable(cg, callee)

    // TODO: use mods first, then use prods to decide whether to drop or not. only compute prods for an individual constraint
    if (AGGRESSIVE_CALLEE_CONSTRAINT_DROPPING) {
      // +1 to account for the fact that callee has not been added to the call stack yet
      val k = Options.MAX_CALLSTACK_DEPTH - (qry.callStack.size + 1)
      assert(k >= 0)

      // purposely getting producers rather than modifiers; we need to drop all constraints with producers in the callee in order to be sound,
      // but it is sound (and more precise) not to drop constraints that can cause a refutation in the callee
      val constraintModMap = rr.getConstraintModifierMap(qry, ignoreLocalConstraints = true)
      //val constraintProdMap = rr.getConstraintProducerMap(qry, ignoreLocalConstraints = true)
      val kReachable = GraphUtil.kBFS(cg, callee, k)

      // TODO: could do something slightly more consistent here like only dropping when no nodes are k-reachable,
      // or dropping all constraints produceable in non-k-reachable nodes
      // the call is relevant if one or more nodes are k-reachable from callee
      // we will drop constraints from all nodes that not k-reachable
      constraintModMap.exists(entry =>
        entry._2.exists(pair => {
        val node = pair._1
        calleeReachable.contains(node) && { // node is reachable from callee
          val isKReachable = kReachable.contains(node)
          if (!isKReachable && qry.heapConstraints.contains(entry._1) &&
              rr.getProducers(entry._1, qry).exists(pair => pair._1 == node))
            // if node not k-reachable from callee AND node contains a producer statement for the current constraint, the node is relevant
            qry.removeConstraint(entry._1) // node not k-reachable. drop constraints
          else if (DEBUG) {
            println(s"callee is relevant: ${ClassUtil.pretty(callee)} because transitive callee is relevant: ${ClassUtil.pretty(node)}")
            val finder = new BFSPathFinder(cg, callee, node)
            val path = finder.find()
            println("Path is: "); path.foreach(n => println(ClassUtil.pretty(n)))
          }
          // if isKReachable is true, the callee is relevant and we will exit via the double exists above
          isKReachable
        }})
      )
    } else {
      val constraintModMap = rr.getConstraintModifierMap(qry, ignoreLocalConstraints = true)
      constraintModMap.exists(entry => entry._2.exists(pair => {
        val node = pair._1
        val rel = calleeReachable.contains(node)
        if (rel && DEBUG) {
          println(s"Callee is relevant: ${ClassUtil.pretty(callee)} because transitive callee is relevant: ${ClassUtil.pretty(node)}")
          print("Instr "); ClassUtil.pp_instr(pair._2, node.getIR()); println(s" relevant to constraint ${entry._1}")
          val finder = new BFSPathFinder(cg, callee, node)
          val path = finder.find()
          println("Path is: "); path.foreach(n => println(ClassUtil.pretty(n)))
        }
        rel
      }))
    }
  }

  def dropCallConstraints(qry : Qry, callee : CGNode, rr : RelevanceRelation, cg : CallGraph,
                          getReachable : (CallGraph, CGNode) => Set[CGNode] = defaultGetReachable) : Unit = {
    val reachable = getReachable(cg, callee)

    val constraintProdMap = rr.getConstraintModifierMap(qry, ignoreLocalConstraints = true)
    constraintProdMap.foreach(pair => {
      val (constraint, producers) = pair
      producers.find(pair => reachable.contains(pair._1)) match {
        case Some(snk) =>
          qry.removeConstraint(constraint)
          if (DEBUG) {
            println("Dropping " + constraint + " due to reachability")
            val finder = new BFSPathFinder(cg, callee, snk._1)
            val path = finder.find()
            println("Path is: ");
            path.foreach(n => println(ClassUtil.pretty(n)))
          }
        case None => ()
      }
    })
  }

}

/** extension of ordinary Thresher transfer functions using the relevance relation to do some things more precisely/efficiently */
class JumpingTransferFunctions(cg : CallGraph, hg : HeapGraph[InstanceKey], hm : HeapModel, cha : IClassHierarchy,
                                 val rr : RelevanceRelation) extends TransferFunctions(cg, hg, hm, cha) {

  override def isCallRelevant(i : SSAInvokeInstruction, caller : CGNode, callee : CGNode, qry : Qry) : Boolean =
    isRetvalRelevant(i, caller, qry) || doesCalleeModifyHeap(callee, qry, rr, cg)

  override def dropCallConstraints(qry : Qry, callee : CGNode,
                                   modRef : java.util.Map[CGNode,com.ibm.wala.util.intset.OrdinalSet[PointerKey]],
                                   loopDrop : Boolean) : Unit =
    JumpingTransferFunctions.dropCallConstraints(qry, callee, rr, cg)

}