package edu.colorado.hopper.util

import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.cfg.ExceptionPrunedCFG
import com.ibm.wala.ssa.{ISSABasicBlock, SSAInstruction, SSAInvokeInstruction}
import com.ibm.wala.util.collections.CollectionFilter
import com.ibm.wala.util.graph.Graph
import com.ibm.wala.util.graph.traverse.{Topological, DFSAllPathsFinder, DFSPathFinder}
import edu.colorado.hopper.piecewise.RelevanceRelation
import edu.colorado.hopper.state.Path
import edu.colorado.walautil.ClassUtil

import scala.collection.JavaConversions._

class ProgramStats(val rr : RelevanceRelation) {
  val cg = rr.cg

  // create a map from each procedure to the number of control-flow paths in that procedure
  val nodeCostMap = {
    val topoIter = Topological.makeTopologicalIter(cg)
    // foldRight is important here -- foldLeft does root-first traversal. we want leaf-first
    topoIter.foldRight (Map.empty[CGNode, Long]) ((n, m) => n.getIR match {
      case null => m
      case ir if n.getMethod.isClinit || n.getMethod.isSynthetic || ClassUtil.isLibrary(n) => m // ignoring library code
      case ir =>
        val cfg = ExceptionPrunedCFG.make(ir.getControlFlowGraph)
        m + (n -> countCFGPaths(cfg.entry(), cfg.exit(), n, m))
    })
  }

  /** count the number of paths between @param src and @param snk in @param g */
  def foldPaths[T,V](src : T, snk : T, g : Graph[T], f : (V, List[T]) => V, acc : V) : V = {

    @annotation.tailrec
    def enumeratePathsRec(finder : DFSPathFinder[T], acc : V) : V = finder.find() match {
      case null => acc
      case path => enumeratePathsRec(finder, f(acc, path.toList))
    }

    //val finder = new DFSPathFinder[T](g, src, new CollectionFilter(java.util.Collections.singleton(snk)))
    val finder = new DFSAllPathsFinder[T](g, src, new CollectionFilter(java.util.Collections.singleton(snk)))
    enumeratePathsRec(finder, acc)
  }

  // the cost of an instruction is the sum of the costs of possible callees (for a call instruction) or 1 (otherwise)
  def getCostOfInstruction(i : SSAInstruction, n : CGNode, nodeCostMap : Map[CGNode,Long]) = i match {
    case i : SSAInvokeInstruction =>
      val targets = cg.getPossibleTargets(n, i.getCallSite)
      //targets.foreach(n => println("Cost of " + n + " is " + nodeCostMap.getOrElse(n, 0L)))
      if (targets.isEmpty) 1L
      else
        // sum the costs of possible callees, counting a callee as free if we don't have a cost summary for it
        targets.foldLeft (0L) ((sum, n) => sum + nodeCostMap.getOrElse(n, 0L)) match {
          case 0L => 1L
          case n => n
        }
    case _ => 1L
  }

  // get the number of paths from src to snk in the cfg for n (factoring in number of paths in callees)
  def countCFGPaths(src : ISSABasicBlock, snk : ISSABasicBlock, n : CGNode, nodeCostMap : Map[CGNode, Long]) : Long = n.getIR match {
    case null => 1L
    case ir if n.getMethod.isSynthetic => 1
    case ir =>
      val cfg = ExceptionPrunedCFG.make(ir.getControlFlowGraph)
      def sumPaths(pathsSoFar : Long, path : List[ISSABasicBlock]) : Long = {
        //path.foreach(blk => print(blk.getNumber + " ")); println
        path.foldLeft (1L) ((pathCost, blk) =>
          if (blk.getLastInstructionIndex >= 0) {
            val instrCost = getCostOfInstruction(blk.getLastInstruction, n, nodeCostMap)
            pathCost * instrCost
          } else pathCost
        ) + pathsSoFar
      }
      // compute the cost of each path, sum them, update the map accordingly
      foldPaths(src, snk, cfg, sumPaths, 0L)
  }

  // count the number of control-flow paths from the beginning of the program to the pc in @param p
  def countControlFlowPathsTo(p : Path) : Long = {

    val (upSet, edgeInstrMap) = rr.computeUpSet(p)
    upSet.foldLeft(1L)((costSoFar, pair) => {
      val (n, _) = pair
      n.getIR match {
        case null => costSoFar
        case ir if n == cg.getFakeRootNode => costSoFar
        case ir =>
          val cfg = ir.getControlFlowGraph
          val entry = cfg.entry()
          val costOfN =
            if (n == p.node) countCFGPaths(entry, p.blk, n, nodeCostMap)
            else {
              val edgeInstrs = edgeInstrMap.getOrElse(n, sys.error(s"Couldn't find $n p is ${p.node}"))
              // sum the paths to each edge instruction. this gives the number of paths in the current node
              edgeInstrs.foldLeft(1L)((cost, edgeInstr) => {
                // get the number of paths from the entry node to the edge instruction
                val snk = ir.getBasicBlockForInstruction(edgeInstr)
                countCFGPaths(entry, snk, n, nodeCostMap) + cost
              })
            }
          assert(costOfN > 0, "Bad cost!")
          assert(costSoFar > 0, "Bad cost!")
          // total cost is the number of paths so far * cost of paths in N
          costOfN * costSoFar
      }
    })
  }

}
