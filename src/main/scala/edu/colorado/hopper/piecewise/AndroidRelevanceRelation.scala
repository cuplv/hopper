package edu.colorado.hopper.piecewise

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.classLoader.IMethod
import com.ibm.wala.ipa.callgraph.propagation.{HeapModel, InstanceKey, LocalPointerKey, PointerKey}
import com.ibm.wala.ipa.callgraph.{CGNode, CallGraph}
import com.ibm.wala.ipa.cfg.PrunedCFG
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ssa._
import com.ibm.wala.util.graph.impl.GraphInverter
import com.ibm.wala.util.graph.traverse.{BFSIterator, BFSPathFinder}
import com.ibm.wala.util.intset.OrdinalSet
import edu.colorado.hopper.state._
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

  // TODO: there's some unstated precondition on the kind of relevant instructions for being able to to do
  // control-feasibility filtering at all...something like "constraints must be fields of the
  // *same* object instance whose methods we are trying to filter, and writes to fields of that object must be through
  // the "this" pointer, or something like that". alternatively, the class whose methods are under consideration is one
  // that is somehow known or proven to have only one instance in existence at a time.

  override def getNodeRelevantInstrsMap(q : Qry, ignoreLocalConstraints : Boolean) : Map[CGNode,Set[SSAInstruction]] = {
    val nodeModifierMap = super.getNodeModifierMap(q, ignoreLocalConstraints)
    // TODO: here, the assume is the conditional block, but to add constraints we need to know which successor of the conditional block
    // we came from--figure out how to save this information
    // simple approach if the false branch does not dominate a relevant instruction, pick it; ditto for the true branch
    val nodeModMapWithAssumes = getDominatingAssumesForRelevantInstructions(nodeModifierMap)

    // TODO: augment with set of reached blocks so we can check if the entry block was reached
    @annotation.tailrec
    def filterRelevantInstrsRec(iter : BFSIterator[ISSABasicBlock],
                                allRelInstrs : Set[SSAInstruction],
                                filteredRelInstrs : Set[SSAInstruction] = Set.empty[SSAInstruction],
                                reachedBlocks : Set[ISSABasicBlock] = Set.empty[ISSABasicBlock]) : (Set[SSAInstruction], Set[ISSABasicBlock]) =
      if (iter.hasNext) {
        val blk = iter.next()

        // assuming that each block contains only one relevant instruction and that it is the last one--this is safe
        // given the way WALA translates
        val newFilteredRelInstrs =
          blk.find(instr => allRelInstrs.contains(instr)) match {
            case Some(instr) => filteredRelInstrs + instr
            case None => filteredRelInstrs
          }
        filterRelevantInstrsRec(iter, allRelInstrs, newFilteredRelInstrs, reachedBlocks + blk)
      } else (filteredRelInstrs, reachedBlocks)

    def isCallableFrom(snk : CGNode, src : CGNode) : Boolean = {
      val path = new BFSPathFinder(cg, src, snk).find()
      // TODO: this is *very* unsound, but need to do it for now to avoid absurd paths. fix CG issues that cause this later
      // I think these CG paths happen whenever a function call places a message on the event queue--this starts a thread
      // that calls dispatchMessage() and then can pull *any* message off of the event queue. We can prevent this from
      // happening by cutting off paths that pass through Handler.dispatchMessage() (or Looper.loop())
      val reachable =
        path != null && path.size > 0 && path.exists(n => n != src && n != snk && !ClassUtil.isLibrary(n)) &&
          path.size < 20
      if (reachable) {
        println(s"can't filter $src since it may transitively call ${ClassUtil.pretty(snk)}")
        path.foreach(println)
      }
      reachable
    }

    case class RelevantNodeInfo(val relevantInstrs : Set[SSAInstruction], val callableFromCurNode : Boolean,
                                val instructionsFormCut : Boolean)

    val curNode = q.node
    // filter the relevant instructions in each node based on their ordering in the CFG (keep instructions forming a cut
    // of the CFG consisting of relevant instructions only) if it is sound to do so based on the call grah
    val intraprocFilteredNodeModMap =
      nodeModMapWithAssumes.map(entry => {
        val (node, relInstrs) = entry
        // not sound to do intraproc filtering if curNode can be (transitively) called from node; have to consider the
        // possibility that we entered curNode "from the middle" instead of from the exit block
        // TODO: we can be more precise than this by still doing intraproc filtering, but starting from all call sites
        //  in node that may (transitively) call curNode rather than from the exit block of node
        val isCallableFromCurNode = isCallableFrom(curNode, node)
        if (isCallableFromCurNode)
          node ->
            RelevantNodeInfo(relInstrs, callableFromCurNode = isCallableFromCurNode, instructionsFormCut = false)
        else {
          val (generatedInstrs, otherInstrs) = relInstrs.partition(i => IRUtil.isGeneratedInstruction(i))
          if (otherInstrs.isEmpty)
            node -> RelevantNodeInfo(relInstrs, callableFromCurNode = isCallableFromCurNode, instructionsFormCut = true)
          else {
            if (DEBUG) {
              println("Before filtering")
              relInstrs.foreach(i => { ClassUtil.pp_instr(i, node.getIR); println })
            }
            val cfg = node.getIR.getControlFlowGraph
            // perform backward BFS that terminates search along a path when it hits a relevant instruction
            val iter =
              new BFSIterator[ISSABasicBlock](cfg, cfg.exit()) {
                override def getConnected(blk: ISSABasicBlock) =
                  if (blk.exists(instr => relInstrs.contains(instr))) java.util.Collections.emptyIterator()
                  // TODO: this isn't sound w.r.t exceptions--make sure none of the relevant instructions aren't
                  // contained in a try block
                  else cfg.getNormalPredecessors(blk).iterator()
              }
            val (filteredInstrs, reachedBlocks) = filterRelevantInstrsRec(iter, otherInstrs)
            // if the filtering search did not reach the entry block, we found a cut in the CFG consisting only of
            // relevant blocks
            val relevantInstructionsFormCut = !reachedBlocks.contains(cfg.entry())
            val finalRelevantInstrs =
              if (relevantInstructionsFormCut) filteredInstrs else filteredInstrs ++ generatedInstrs
            assert(!finalRelevantInstrs.isEmpty, "Filtered instructions empty--something went very wrong")
            if (DEBUG) {
              println(s"Found relevant cut? $relevantInstructionsFormCut")
              println("After filtering")
              finalRelevantInstrs.foreach(i => { ClassUtil.pp_instr(i, node.getIR); println })
            }
            node ->
              RelevantNodeInfo(finalRelevantInstrs, callableFromCurNode = isCallableFromCurNode,
                instructionsFormCut = relevantInstructionsFormCut)
          }
        }
      })

    // we can filter if toFilter is a constructor o.<init>() and one of otherRelNodes is a method o.m()
    def canFilterDueToConstructor(toFilter : CGNode, nodeRelevanceMap : Map[CGNode,RelevantNodeInfo]) : Boolean = {
      val toFilterMethod = toFilter.getMethod
      toFilterMethod.isInit &&
        nodeRelevanceMap.keys.exists(n =>
          n != toFilter && {
            val m = n.getMethod
            !m.isInit && !m.isClinit
            m.getDeclaringClass == toFilterMethod.getDeclaringClass
          } && nodeRelevanceMap(n).instructionsFormCut
        )
    }

    // similarly, we can filter if toFilter is a class initializer o.<clinit> and one of otherRelNodes is a method o.m()
    def canFilterDueToClassInit(toFilter : CGNode, nodeRelevanceMap : Map[CGNode,RelevantNodeInfo]) : Boolean = {
      val toFilterMethod = toFilter.getMethod
      toFilterMethod.isClinit &&
        nodeRelevanceMap.keys.exists(n =>
          n != toFilter && n.getMethod.getDeclaringClass == toFilterMethod.getDeclaringClass &&
          nodeRelevanceMap(n).instructionsFormCut
        )
    }

    intraprocFilteredNodeModMap.foldLeft (Map.empty[CGNode,Set[SSAInstruction]]) ((m, entry) => {
      val (toFilter, relInfo) = entry
      // can refute if there's no way to get from curNode to toFilter
      if (isNotBackwardReachableFrom(toFilter, curNode)) m
      else if (relInfo.callableFromCurNode) {
        if (DEBUG) println(s"${ClassUtil.pretty(curNode)} callable from ${ClassUtil.pretty(toFilter)}, can't filter")
        m + (toFilter -> relInfo.relevantInstrs)
      } else
        // try to filter
        if (canFilterDueToConstructor(toFilter, intraprocFilteredNodeModMap) ||
            canFilterDueToClassInit(toFilter, intraprocFilteredNodeModMap)) {
          if (DEBUG) println(s"Filtered node $toFilter!")
          // TODO: add canFilterDueToMethodOrdering
          m
        } else {
          if (DEBUG) println(s"Can't filter node $toFilter due to lack of ordering constraints")
          m + (toFilter -> relInfo.relevantInstrs)
        }
    })
  }

  def getDominatingAssumesForRelevantInstructions(nodeInstrMap : Map[CGNode,Set[SSAInstruction]]) : Map[CGNode,Set[SSAInstruction]] = {
    def getDominatingCondBlks(blk : ISSABasicBlock,
                              cfg : PrunedCFG[SSAInstruction,ISSABasicBlock]) : Iterable[ISSABasicBlock] = {
      val bwReachable = CFGUtil.getBackwardReachableFrom(blk, cfg, inclusive = true)
      bwReachable.filter(blk => CFGUtil.isConditionalBlock(blk) &&
                                cfg.getSuccNodes(blk).exists(blk => !bwReachable.contains(blk)))
    }

    nodeInstrMap.map(entry => {
      val (node, relInstructions) = entry
      val ir = node.getIR
      val cfg = CFGUtil.getBackEdgePrunedCFG(ir.getControlFlowGraph)
      val newRelInstructions =
        relInstructions.foldLeft (relInstructions) ((relInstructions, i) => {
          if (IRUtil.isGeneratedInstruction(i)) relInstructions
          else CFGUtil.findInstr(ir, i) match {
            case Some((blk, _)) =>
              getDominatingCondBlks(blk, cfg).foldLeft (relInstructions) ((relInstructions, blk) => {
                blk.foldLeft (relInstructions) ((relInstructions, i) => i match {
                  case i : SSAConditionalBranchInstruction => relInstructions + i
                  case _ => relInstructions
                })
              })
            case None => relInstructions
          }
        })
      node -> newRelInstructions
    })
  }


  /** @return conditionals that compare objects pointed to by @param q to null */
  def getRelevantAssumes(q : Qry) : Set[(CGNode,SSAConditionalBranchInstruction)] = {
    def getRelevantAssumesForLocalPointers(localPointers : Iterable[LocalPointerKey],
                                           s : Set[(CGNode,SSAConditionalBranchInstruction)]) = {
      // find conditionals in the IR that compare one of the LPK's to null
      val lpksByNode =
        localPointers.groupBy(k => k.getNode).map(entry => {
          val (node, vals) = entry
          node -> vals.map(k => k.getValueNumber)
        })
      lpksByNode.foldLeft (s) ((s, entry) => {
        val (node, valueNums) = entry
        node.getIR match {
          case null => s
          case ir =>
            val tbl = ir.getSymbolTable
            ir.iterateAllInstructions().foldLeft (s) ((s, i) => i match {
              case i : SSAConditionalBranchInstruction =>
                val (use0, use1) = (i.getUse(0), i.getUse(1))
                if ((valueNums.contains(use0) || valueNums.contains(use1)) &&
                  (tbl.isNullConstant(use0) || tbl.isNullConstant(use1)))
                  s + ((node, i))
                else s
              case _ => s
            })
        }
      })
    }

    def getLocalPredsOfSuccs(k : PointerKey,
                             s : Set[LocalPointerKey] = Set.empty[LocalPointerKey]) : Set[LocalPointerKey] =
      hg.getSuccNodes(k).foldLeft (s) ((s, k) =>
        hg.getPredNodes(k).foldLeft (s) ((s, k) => k match {
          case k: LocalPointerKey => s + k
          case _ => s
        })
      )

    q.heapConstraints.foldLeft (Set.empty[(CGNode,SSAConditionalBranchInstruction)]) ((s, e) => e match {
      case ObjPtEdge(ObjVar(rgn), InstanceFld(fld), p@PureVar(_)) if q.isNull(p) =>
        // get local pointer keys that point at the value pointed at by fld
        val localPointers =
          rgn.foldLeft (Set.empty[LocalPointerKey]) ((s, k) =>
            getLocalPredsOfSuccs(hm.getPointerKeyForInstanceField(k, fld), s)
          ).filter(k => !ClassUtil.isLibrary(k.getNode))
        getRelevantAssumesForLocalPointers(localPointers, s)
      case StaticPtEdge(_, StaticFld(fld), p@PureVar(_)) if q.isNull(p) =>
        val localPointers = getLocalPredsOfSuccs(fld)
        getRelevantAssumesForLocalPointers(localPointers, s)
      case _ => s
    })
  }

}
