package edu.colorado.scwala.piecewise

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.ipa.callgraph.{CGNode, CallGraph}
import com.ibm.wala.ipa.callgraph.propagation.{HeapModel, InstanceKey, LocalPointerKey}
import com.ibm.wala.ipa.cfg.ExceptionPrunedCFG
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ssa.{ISSABasicBlock, SSAArrayLoadInstruction, SSAArrayStoreInstruction, SSACFG, SSAGetInstruction, SSAInstruction, SSAInvokeInstruction, SSANewInstruction, SSAPhiInstruction, SSAPutInstruction, SSAReturnInstruction, SymbolTable}
import com.ibm.wala.util.graph.dominators.Dominators
import com.ibm.wala.util.graph.impl.GraphInverter
import com.ibm.wala.util.intset.{BasicNaturalRelation, OrdinalSet}
import com.twitter.util.LruMap
import edu.colorado.scwala.piecewise.RelevanceRelation._
import edu.colorado.scwala.solver.UnknownSMTResult
import edu.colorado.scwala.state.{ArrayFld, ArrayPtEdge, Fld, HeapPtEdge, InstanceFld, LocalPtEdge, LocalVar, ObjPtEdge, ObjVar, Path, PtEdge, Pure, PureVar, Qry, ReturnVar, StaticFld, StaticPtEdge, Val, Var}
import edu.colorado.scwala.util.Types._
import edu.colorado.scwala.util.{CFGUtil, CGNodeUtil, ClassUtil, IRUtil, PtUtil, Util}
import edu.colorado.thresher.core.{Options, WALACFGUtil}

import scala.collection.JavaConversions._



object RelevanceRelation {
  // should we use the UP and down set to help us decide where to jump?
  // if this is not enabled, we'll behave more or less like a flow-insensitive analysis interprocedurally
  val USE_REACHABILITY_INFO = false
  // should we do a local dominator analysis to cut down on the number of relevant instructions to fork to?
  // if this is enabled, we are flow-sensitive intraprocedurally
  val DO_DOMINATOR_CHECK = true
  val DEBUG = false
  val CACHE_SIZE = 100 
}

class RelevanceRelation(val cg : CallGraph, val hg : HeapGraph, val hm : HeapModel, val cha : IClassHierarchy,
  val cgTransitiveClosure : java.util.Map[CGNode,OrdinalSet[CGNode]] = null) { // TODO: extract relevance relation that doesn't need this
  val producerCache = new LruMap[PtEdge, List[(CGNode,SSAInstruction)]](CACHE_SIZE) 
 
  def cleanup() : Unit = {
    producerCache.clear
  }  
  
  /** get backward reachable instr from @param blk in @param node without exceptional control flow */
  def getReachableInstrs(blk : ISSABasicBlock, node : CGNode) : Set[SSAInstruction] = {
    val cfg = ExceptionPrunedCFG.make(node.getIR().getControlFlowGraph()) // ignoring exceptions for now
    CFGUtil.getBackwardReachableFrom(blk, cfg, inclusive = false).foldLeft (Set.empty[SSAInstruction]) ((set, blk) => 
      blk.asInstanceOf[SSACFG#BasicBlock].getAllInstructions().foldLeft (set) ((set, instr) => set + instr))
  }
  
  /**
   * @return a map whose keys are the set of methods that may be on the call stack when method of p.node is called
   * each CGNode in the key set maps to the set of instructions that may be executed before a call to the method of p.node
   */ 
  def computeUpSet(p : Path) : (Map[CGNode,MSet[SSAInstruction]], MMap[CGNode,Set[SSAInstruction]])  = {    
    val edgeInstrMap = Util.makeMap[CGNode,Set[SSAInstruction]]

    def addEdgeInstr(node : CGNode, instr : SSAInstruction) : Unit = {
      val edgeCalls = edgeInstrMap.getOrElse(node, Set.empty[SSAInstruction])
      edgeInstrMap += (node -> (edgeCalls +  instr))
    }
    
    // the edges backward reachable from the start node
    val relevantEdges = new BasicNaturalRelation()
    // the edges we have already processed (recursion safety net)
    val processed = Util.makeSet[(Int,Int)]

    def makeWorklistFor(callee : CGNode, worklist : List[(CGNode,CGNode)] = List.empty) : List[(CGNode,CGNode)] = {
      val calleeId = callee.getGraphNodeId()
      // add pred -> caller edges to the worklist and relevant node list
      cg.getPredNodes(callee).foldLeft (worklist) ((worklist, pred) => {
        relevantEdges.add(pred.getGraphNodeId(), calleeId) 
        (pred, callee) :: worklist
      })               
    }        
    
    @annotation.tailrec
    def computeUpSetRec(worklist : List[(CGNode, CGNode)], upSet : Map[CGNode,MSet[SSAInstruction]]) : Map[CGNode,MSet[SSAInstruction]] = 
      worklist match {
        case (caller, callee) :: rest =>
          val (callerNum, calleeNum) = (caller.getGraphNodeId(), callee.getGraphNodeId())
          val reachable = upSet.getOrElse(caller, Util.makeSet[SSAInstruction])
                    
          val sites = cg.getPossibleSites(caller, callee).toSet
          val callInstrs = IRUtil.getAllInstructions(caller).collect({ case i : SSAInvokeInstruction if sites.contains(i.getCallSite()) => i })
          callInstrs.foreach(call => {
            addEdgeInstr(caller, call)
            val callBlk = CFGUtil.findInstr(caller, call) match {
              case Some((callBlk,_)) => callBlk
              case None => sys.error("couldn't find " + call + " in " + caller)
            }
            val reach = getReachableInstrs(callBlk, caller) // get reachableInstrs is non-inclusive
            reachable ++= reach 
          })
            
          // make a note that we've processed this (caller, callee) pair
          relevantEdges.remove(callerNum, calleeNum)
          // if we have processed all of the relevant callees for this caller
          val newWorklist = if (relevantEdges.getRelatedCount(callerNum) == 0) {
            if (processed.add(callerNum, calleeNum) && 
                 // TODO: this isn't sound, but is needed to avoid extreme imprecision. decide what to do with this later
                !ClassUtil.isLibraryToApplicationCall(caller, callee)) {
              //assert(processed.add(caller), "recursion from " + caller + " detected")
              //println("_EDGE: " + ClassUtil.pretty(caller) + " -> " + ClassUtil.pretty(callee))
              makeWorklistFor(caller, rest)
            } else rest
          } else rest
          // is this our first time processing caller?
          val newUpSet = if (!upSet.contains(caller)) upSet + (caller -> reachable) else upSet
          computeUpSetRec(newWorklist, newUpSet)
        case Nil => upSet      
      }
    
    val callStack = p.callStackIter
    var first = true
    // compute UP for all nodes on the call stack of the current path
    val upSet = callStack.foldLeft (Map.empty[CGNode,MSet[SSAInstruction]]) ((map, frame) => {
      if (!first) {
        // find the edge call for this stack frame
        // + 1 because we always decrement the index of a path before we execute the instruction at index
        val index = frame.index + 1
        val blkInstrs = frame.blk.asInstanceOf[SSACFG#BasicBlock].getAllInstructions()
        if (index < blkInstrs.size()) {
          blkInstrs.get(index) match {
            case i : SSAInvokeInstruction => addEdgeInstr(frame.node, blkInstrs.get(index))
            case i => sys.error("Unexpected edge instr " + i + " node " + frame.node + " IR " + frame.node.getIR())
          }        
        }
      } else first = false // the first call stack frame does not have an edge call
      // TODO: again, check if getReachableInstrs is inclusive
      map + (frame.node -> (Util.makeSet[SSAInstruction] ++= getReachableInstrs(frame.blk, frame.node)))       
    })
    
    // worklist consists only of the last node on the call stack, since we do not know its caller(s)
    // for other nodes on the call stack, we know their calling context 
    val worklist = makeWorklistFor(callStack.last.node)    
    // setup worklist with preds of current node and get backward reachable instructions from current node 
    (computeUpSetRec(worklist, upSet), edgeInstrMap)  
  }
  
  /**
   * @return a map whose key set is the same as the key set of @param upSet
   * each CGNode in the key set maps to the set of CGNode's that may be called (directly or transitively) from that node given that
   * only the instructions in the value set of @param upSet are reachable
   */
  def computeDownSet(upSet : Map[CGNode,MSet[SSAInstruction]], edgeInstrMap : MMap[CGNode,Set[SSAInstruction]]) : Map[CGNode, MSet[CGNode]]= {
    val map = upSet.foldLeft (Map.empty[CGNode,MSet[CGNode]]) ((map, pair) => {
      val (node, reachable) = pair
      val downReachable = Util.makeSet[CGNode]
      
      // handle edge calls -- add them to the reachable instrs for the UP set, but do not allow them (or their callees)
      // to be considered as part of the DOWN set
      val edgeCalls = edgeInstrMap.getOrElse(node, Set.empty[SSAInvokeInstruction]).map(i => i match {
        case i : SSAInvokeInstruction => i
        case other => sys.error("bad edge instr " + other)
      })
      reachable ++= edgeCalls
      
      // find each reachable call in node and add the call graph transitive closure of the nodes reachable from the call to the down set
      reachable.collect({ case i : SSAInvokeInstruction if !edgeCalls.contains(i) =>
        cg.getPossibleTargets(node, i.getCallSite()).foreach(target => {
        //cg.getNodes(i.getDeclaredTarget()).foreach(target => {
        //getSuccs(target, cg, 1) // for instrumentation purposes
        if (!downReachable.contains(target)) (downReachable ++= OrdinalSet.toCollection(cgTransitiveClosure.get(target)) += target)
      })})
      map + (node -> downReachable)
    })
    
    // annoying special case for fakeWorldClinit. 
    // the problem is that cg.getNodes(invoke fakeWorldClinit()) does not return the fakeWorldClinit node. 
    // add it and its transitive closure explicitly instead
    //val fakeWorldClinit = WALACFGUtil.getFakeWorldClinitNode(cg)
    val fakeWorldClinit = CGNodeUtil.getFakeWorldClinitNode(cg).get
    map +
      (fakeWorldClinit -> (Util.makeSet[CGNode] ++= (OrdinalSet.toCollection(cgTransitiveClosure.get(fakeWorldClinit)))))
  }
  
  def computeUpAndDownSet(p : Path) : (Map[CGNode,MSet[SSAInstruction]], Map[CGNode, MSet[CGNode]])= {
    val (upSet, edgeInstrMap) = computeUpSet(p)
    val downSet = computeDownSet(upSet, edgeInstrMap)
    (upSet, downSet)  
  }
  
  /** return Some(paths) if we should jump, None if we should not jump */
  def getPiecewisePaths(p : Path, jmpNum : Int) : Option[List[Path]] = {   
    if (DEBUG) println("computing relevance graph")    
    if (!p.qry.hasConstraint) {
      println("no constraint " + p.qry)
      return None    
    }

    // get producers
    val prodMap = getNodeProducerMap(p.qry, ignoreLocalConstraints = true)

    if (DEBUG) {
      val producers = prodMap.values.flatten
      println(s"Overall, have ${prodMap.size} producers")
      producers.foreach(println)
    }
     
    if (!USE_REACHABILITY_INFO && !DO_DOMINATOR_CHECK) {
      p.clearCallStack 
      Some(prodMap.foldLeft (List.empty[Path]) ((paths, pair) => Path.fork(p, pair._1, pair._2, jmpNum, cg, hg, hm, cha, paths)))
    } else if (!USE_REACHABILITY_INFO) {
      val curNode = p.node
      p.clearCallStack
      // TODO: it's not always sound to do the dominator filtering without the up set. the problem is that we could enter the method 
      // from many different places (callees) and even if one relevant instruction dominates the other, we might enter from a callee
      // that lets us skip that instruction
      Some(prodMap.foldLeft (List.empty[Path]) ((paths, pair) =>
        if (curNode == pair._1) Path.fork(p, pair._1, pair._2, jmpNum, cg, hg, hm, cha, paths) // current node same as relevant node. not (necessarily) sound to do filtering
        else doLocalDominatorFiltering(p, pair._1, pair._2, jmpNum, paths)))
    } else {
      // get reachability informaton
      val (upSet, downSet) = computeUpAndDownSet(p)
      val downSetAll = downSet.values.toSet.flatten
      val curNode = p.node
      p.clearCallStack // this needs to be done *after* computing UP set
      val paths = prodMap.foldLeft (List.empty[Path]) ((paths, pair) => {
        val (relevantNode, instrs) = pair
        // if neither the up set nor the down set contains the relevant node/instruction, we can skip it because it is unreachable
        // TODO: should perhaps add context to nodes when we jump (particularly if they're in the up set)
        if (downSetAll.contains(relevantNode)) {
          if (DEBUG) println("DOWN set contains " + relevantNode)
          // since DOWN set contains the node, all producer instructions are reachable. fork a path for each one
          if (DO_DOMINATOR_CHECK && curNode != relevantNode) doLocalDominatorFiltering(p, relevantNode, instrs, jmpNum, paths)
          else Path.fork(p, relevantNode, instrs, jmpNum, cg, hg, hm, cha, paths)
        } else if (upSet.contains(relevantNode)) {
          if (DEBUG) println("UP set contains " + relevantNode)   
          // even if a relevant node is in the UP set, the instruction(s) that make the node
          // relevant may not be reachable. filter the set of relevant instructions in the UP
          // set by the set of reachable instructions
          val reachableInstrs = upSet.getOrElse(relevantNode, Set.empty[SSAInstruction])
            
          Path.fork(p, relevantNode, instrs.intersect(reachableInstrs), jmpNum, cg, hg, hm, cha, paths)
          // TODO: would be good to allow dominator check filtering here as well, but it is actually quite complicated
          // the problem is that we can't just do the dominator check over instrs \cap reachableInstrs. instead, we need to consider
          // set of backward reachable instrs from each method call M in edge calls and perform the dominator check over bwReach(M) \cap instrs
        } else paths
      })
      Some(paths)
    }        
  }  
  
  /** filter the reachable instruction so that we only consider the ones that we would hit first when going backwards */
  def doLocalDominatorFiltering(p : Path, relevantNode : CGNode, instrs : Set[SSAInstruction], jmpNum : Int, paths : List[Path]) : List[Path] = {    
    if (DEBUG) println("Doing dominator filtering for " + ClassUtil.pretty(relevantNode))
    val (blkMap, initInstrs) = instrs.foldLeft (Map.empty[ISSABasicBlock,(SSAInstruction,Int)], Set.empty[SSAInstruction]) ((pair ,instr) => {
      // initInstrs is the set of instructions that do not belong to any block in the CFG. this occurs because we
      // generate our own "initialization to default values" instructions that do not occur in any block
      val (blkMap, initInstrs) = pair 
      CFGUtil.findInstr(relevantNode, instr) match {
        case Some((blk, index)) => 
          val newMap = blkMap.get(blk) match {
            case Some((oldInstr,oldIndex)) =>
              assert (Util.implies(oldInstr == instr, oldIndex == index))
              if (oldIndex > index) blkMap // if the (instr, index) pair already in the map is at a *higher* index, keep it. 
              else blkMap + (blk -> (instr, index)) // otherwise, replace it with the new pair
            case None => blkMap + (blk -> (instr, index)) // no pair in the map yet, add this one
          }
          (newMap, initInstrs)
        case None => (blkMap, initInstrs + instr) // found initInstr -- add it to the list
      }
    })
       
    if (blkMap.isEmpty) 
      // all the instructions are init/clinit instrs. fork on these; p.fork takes care of considering all initInstrs as a single case
      // instead of forking a separate case for each (which would be silly)
      Path.fork(p, relevantNode, initInstrs, jmpNum, cg, hg, hm, cha, paths)
    else {         
      val cfg = relevantNode.getIR().getControlFlowGraph()
      val reversedExceptionFreeCFG = GraphInverter.invert(ExceptionPrunedCFG.make(cfg))
      assert (reversedExceptionFreeCFG.containsNode(cfg.exit()), 
              "exit block " + cfg.exit() + " should be in " + reversedExceptionFreeCFG + " but it's not. ir is " + relevantNode.getIR())
      val domInfo = Dominators.make(reversedExceptionFreeCFG, cfg.exit())
      val domGraph = domInfo.getGraph()
      val blks = blkMap.keys
      // if some block b0 in blkMap is postdominated by a differnt block b1 in blkMap, we don't need to consider jumping to b0
      // because we will always end up visiting b1 first
      val filtered = blkMap.foldLeft (Set.empty[SSAInstruction]) ((instrs, pair) => 
        //if (blks.exists(blk => blk != pair._1 && domInfo.isDominatedBy(pair._1, blk))) instrs
        if (blks.exists(blk => blk != pair._1 && (!domGraph.containsNode(blk) || !domGraph.containsNode(pair._1) || // TODO: filter nodes not in the graph away somewhere
            domInfo.isDominatedBy(pair._1, blk)))) instrs
        else instrs + pair._2._1
      )
      if (DEBUG) { 
        println("after filtering, have " + filtered.size + " relevant instructions (down from " + instrs.size + ")")
        filtered.foreach(i => { ClassUtil.pp_instr(i, relevantNode.getIR()); println })
      }
      // now, filtered only contains instructions at the "leaves" of the CFG. we only need to consider a case for each instr in filtered
      // it is ok not to consider instructions in initInstrs (if any)  because these instructions will always execute before instrs in filtered 
      // (because they are initializations to default values, which are the first instructions to execute in a method) 
      Path.fork(p, relevantNode, filtered, jmpNum, cg, hg, hm, cha, paths)
    }
  }

  def hasUnproduceableConstraint(p : Path) : Boolean = p.qry.hasConstraint && hasUnproduceableConstraint(p, getConstraintProducerMap(p.qry))  
  
  def hasUnproduceableConstraint(p : Path, prodMap : Map[PtEdge, List[(CGNode,SSAInstruction)]]) = {
    val qry = p.qry
    qry.hasConstraint && qry.constraints.exists(e => {            
      val res = !prodMap.contains(e) && !mayBeArrayContentsConstraintHoldingDefaultValue(e, qry)
      if (res && Options.PRINT_REFS) println("Refuted by unproduceable constraint " + e)
      res
      /*
      res || { e match {
        case e : HeapPtEdge =>
          val timer = new Timer
          timer.start
          val res = flowSensitiveRefuted(p, e, prodMap)
          timer.stop
          println("Flow-insensitive check took " + timer.time)
          res
        case _ => false
      }}*/
    })
  }
  
  //def alreadyChecked : MSet[IField]
    
  private def flowSensitiveRefuted(p : Path, e : HeapPtEdge, prodMap : Map[PtEdge, List[(CGNode,SSAInstruction)]]) : Boolean = {
    val prods = prodMap(e)
    if (prods.size == 1 && p.callStackSize == 1) {      
      val (node, instr) = prods.head
      println("got single prod " + ClassUtil.pretty(node))
      val cfg = node.getIR().getControlFlowGraph()
      
      val prodBlk = CFGUtil.findInstr(node, instr) match {
        case Some((blk, _)) => blk     
        case None => sys.error("Couldn't find " + instr + " in " + node)
      }
      
      val reversedExceptionFreeCFG = GraphInverter.invert(ExceptionPrunedCFG.make(cfg))
      val domInfo = Dominators.make(reversedExceptionFreeCFG, cfg.exit())
      // all paths from the entry of the CFG will go through prodBlk if prodBlk dominates
      // the entry block of the cfg in the backward CFG
      if (domInfo.isDominatedBy(cfg.entry(), prodBlk)) {
        println("got dom")
        // now need to look for node in down set
        val (upSet, downSet) = computeUpAndDownSet(p)
        val downSetAll = downSet.values.toSet.flatten
        assert(!upSet.contains(node))
        assert(downSetAll.contains(node))
        
        def flowSensitiveOk(node : CGNode, targetNode : CGNode) : Boolean = {
          // TODO: do dominator check here also?
          val preds = cg.getPredNodes(node).toList
          if (preds.size == 1) {
            val pred = preds.head
            if (downSet(pred).contains(targetNode)) {
               println("pred " + ClassUtil.pretty(pred) + " calls " + ClassUtil.pretty(targetNode) + " directly")
              val sites = cg.getPossibleSites(pred, targetNode).toSet
              assert(!sites.isEmpty)
              val callInstrs = upSet(pred).collect({ case i : SSAInvokeInstruction if sites.contains(i.getCallSite()) => i})
              assert(!callInstrs.isEmpty)
              val tbl = pred.getIR().getSymbolTable()
              // the call is flow-sensitive ok if there's one call that works
              callInstrs.exists(call => {
                instr match {
                  case i : SSAPutInstruction =>
                    if (tbl.isParameter(i.getVal())) {             
                      val rgn = PtUtil.getPt(Var.makeLPK(call.getUse(i.getVal() - 1), pred, hm), hg)
                      e.snk match {
                        case ObjVar(eRgn) => !eRgn.intersect(rgn).isEmpty
                        case _ => sys.error("PureVals.")
                      }
                    } else {
                      sys.error("non-parameter assign")
                      //false
                    }
                  case i => sys.error("Unsupported instruction " + i)
                }
              })
            } else flowSensitiveOk(pred, targetNode)
          } else true
        }
        
        val res = !flowSensitiveOk(p.node, node)
        if (!res && Options.PRINT_REFS) println("Refuted by flow-sensitive check!")
        res
      } else false    
    } else false   
  }
  
  def mayBeArrayContentsConstraintHoldingDefaultValue(e : PtEdge, qry : Qry) : Boolean = e match {
    case ArrayPtEdge(_, _, p@PureVar(_)) =>
      try {
        qry.checkTmpPureConstraint(Pure.makeDefaultValConstraint(p))
      } catch {
        case e : UnknownSMTResult => true
      }
    case _ => false
  }
    
  /**
   * @return map of (modifier CG Node -> modifier commands for that CGNode)
   */
  def getNodeModifierMap(q : Qry, ignoreLocalConstraints : Boolean = false) : Map[CGNode,Set[SSAInstruction]] = 
    getProducerOrModifierMap(q, getNodeProducerOrModifierMapInternal, ignoreLocalConstraints, getMods = false)
  
  /**
   * @return map of (constraint -> (modifier node, modifier commands))
   */
  def getConstraintModifierMap(q : Qry, ignoreLocalConstraints : Boolean = false) : Map[PtEdge,List[(CGNode,SSAInstruction)]] = 
    getProducerOrModifierMap(q, getConstraintProducerOrModifierMapInternal, ignoreLocalConstraints, getMods = false)  
  
  /**
   * @return map of (producer CG Node -> producer commands for that CGNode)
   */
  def getNodeProducerMap(q : Qry, ignoreLocalConstraints : Boolean = false) : Map[CGNode,Set[SSAInstruction]] = 
    getProducerOrModifierMap(q, getNodeProducerOrModifierMapInternal, ignoreLocalConstraints, getMods = false)
  
  /**
   * @return map of (constraint -> (producer node, producer commands))
   */
  def getConstraintProducerMap(q : Qry, ignoreLocalConstraints : Boolean = false) : Map[PtEdge,List[(CGNode,SSAInstruction)]] = 
    getProducerOrModifierMap(q, getConstraintProducerOrModifierMapInternal, ignoreLocalConstraints, getMods = false)
  
  private def getProducerOrModifierMap[K,V](qry : Qry, f : (MSet[_ <: PtEdge], Qry, Map[K,V], Boolean) => Map[K,V],
      ignoreLocalConstraints : Boolean, getMods : Boolean) : Map[K,V] = {
    val map = f(qry.heapConstraints, qry, Map.empty[K,V], getMods)
    // get producers of local constraints for each frame on the call stack
    if (ignoreLocalConstraints) map
    else qry.callStack.stack.foldLeft (map) ((map, fr) => f(fr.localConstraints, qry, map, getMods)) 
  }
  
  private def getNodeProducerOrModifierMapInternal(s : MSet[_ <: PtEdge], q : Qry, 
      map : Map[CGNode,Set[SSAInstruction]], getMods : Boolean) : Map[CGNode,Set[SSAInstruction]] =
    s.foldLeft (map) ((map, e) => {
      val prodsOrMods = if (getMods) getModifiers(e, q) else getProducers(e, q)
      if (DEBUG) {
        println(prodsOrMods.size + " producers for " + e + ": ")
        prodsOrMods.foreach(pair => { ClassUtil.pp_instr(pair._2, pair._1.getIR()); println(" in " + ClassUtil.pretty(pair._1)) }) 
      }        
      prodsOrMods.foldLeft (map) ((map, prod) => {
        val (node, instr) = prod
        val instrs = map.getOrElse(node, Set.empty[SSAInstruction])
        // TODO : do we need to be worried about instructions being identical and being smushed in the set
        // when they in fact represent instructions at distinct program points? Instruction comparison is by
        // address equality, so I don't think this should happen
        map + (node -> (instrs + instr))
      })
    })
    
  private def getConstraintProducerOrModifierMapInternal(s : MSet[_ <: PtEdge], q : Qry, 
      map : Map[PtEdge, List[(CGNode,SSAInstruction)]], getMods : Boolean) : Map[PtEdge, List[(CGNode,SSAInstruction)]] = 
    s.foldLeft (map) ((map, e) => {
      if (DEBUG) println("getting producers for " + e)
      val prods = if (getMods) getModifiers(e, q) else getProducers(e, q)
      if (DEBUG) {
        println(prods.size + " producers for " + e + ": ")
        prods.foreach(pair => { ClassUtil.pp_instr(pair._2, pair._1.getIR()); println(" in " + ClassUtil.pretty(pair._1)) }) 
      }
      if (prods.isEmpty) map else map + (e -> prods)
    })  
  
  private def getLPKNodes(l : Set[LocalPointerKey]) : Set[CGNode] = 
    l.foldLeft (Set.empty[CGNode]) ((set, pred) => set + pred.getNode())
  
  private def arrayIndicesPossiblyEqual(indexUse : Int, fld : ArrayFld, tbl : SymbolTable, qry : Qry) = fld match {
    case ArrayFld(_, _, Some(indexVar)) => !Options.INDEX_SENSITIVITY || !tbl.isConstant(indexUse) || {
      try {
        qry.checkTmpPureConstraint(Pure.makeEqConstraint(indexVar, Pure.makePureVal(tbl, indexUse)))
      } catch {
        case e : UnknownSMTResult => true // SMT solver failed conservatively assume that they may be equal
      }
    }
    case ArrayFld(_, _, None) => true    
  }
  
  private def lhsesEq(lhs : LocalPointerKey, i : SSAInstruction) : Boolean = i.getDef == lhs.getValueNumber    
      
  private def rhsMayEqCheck(rhs : Val, rhsUse : Int, node : CGNode, tbl : SymbolTable, qry : Qry, 
    heapCheck : (Int, CGNode, Set[InstanceKey]) => Boolean, getModifiers : Boolean) : Boolean = getModifiers || { rhs match {
      case ObjVar(rgnRhs) => !tbl.isNullConstant(rhsUse) && heapCheck(rhsUse, node, rgnRhs)
      case p@PureVar(_) =>
        def pureMayEqCheck(useNum : Int, p : PureVar, tbl : SymbolTable, qry : Qry) : Boolean = !tbl.isConstant(useNum) || {
          try
            if (tbl.isStringConstant(useNum)) qry.checkTmpPureConstraint(Pure.makeNeNullConstraint(p))
            // unsupported constraint types -- assume equality
            else if (tbl.isFloatConstant(useNum) || tbl.isDoubleConstant(useNum) || tbl.isLongConstant(useNum)) true
            else qry.checkTmpPureConstraint(Pure.makeEqConstraint(Pure.makePureVal(tbl, useNum), p))
          catch {
            case e : UnknownSMTResult => true // SMT solver failed; conservatively assume that they may be equal
          }
        }                
        pureMayEqCheck(rhsUse, p, tbl, qry)
    }}           
  
  private val nopHeapCheck = (argUse : Int, node : CGNode, rgnRhs : Set[InstanceKey]) => true
    
  /** @return the set of CGNode's that may modify this query's heap constraints. Note that this need not include the current node even if the query has local constraints */
  def getModifierNodes(qry : Qry) : Set[CGNode] = getProducerOrModifierNodes(qry, getModifiers = true)   
  /** @return the set of CGNode's that may produce this query's heap constraints. Note that this need not include the current node even if the query has local constraints */
  def getProducerNodes(qry : Qry) : Set[CGNode] = getProducerOrModifierNodes(qry, getModifiers = false) 
  
  private def getProducerOrModifierNodes(qry : Qry, getModifiers : Boolean) = 
    qry.heapConstraints.foldLeft (Set.empty[CGNode]) ((s, e) => getModifiersOrProducersInternal(e, qry, getModifiers).foldLeft (s) ((s, pair) => s + pair._1))
    
  /** the modifiers for an edge e are the instructions that can write to the variable or address on the LHS of the edge e 
   *  stated differently, the modifier instructions are any instructions that may *change* the concretization of a query consisting of e after execution
   */ 
  def getModifiers(e : PtEdge, qry : Qry) : List[(CGNode, SSAInstruction)] = getModifiersOrProducersInternal(e, qry, getModifiers = true)
  
  /**
   * the producers of an edge e are the instructions that can write to the variable or address on the LHS of the edge e *AND* write a value
   * that is may be equal to the value on the RHS of the edge e. stated differently, the producer instructions are any instructions that may *shrink* the
   * size of the concretization of a query consisting of e after execution. the producers instruction of an edge are a subset of the modifier instructions for an edge
   */
  def getProducers(e : PtEdge, qry : Qry) : List[(CGNode, SSAInstruction)] =
    // don't want to use cache with pure var constraints, as the same pure var may have different values in different theorem
    // prover contexts    
    if (e.snk.isInstanceOf[PureVar] || (Options.INDEX_SENSITIVITY && e.isInstanceOf[ArrayPtEdge])) getModifiersOrProducersInternal(e, qry, getModifiers = false)
    else producerCache.getOrElseUpdate(e, getModifiersOrProducersInternal(e, qry, getModifiers = false))      
  
  private def getProducerOrModifierNodesAndHeapCheck(rgnLhs : Set[InstanceKey], snk : Val, getModifiers : Boolean) : (Set[CGNode], (Int, CGNode, Set[InstanceKey]) => Boolean) = {
    val lhsPreds = PtUtil.getLocalPreds(rgnLhs, hg)
    val lhsNodes = getLPKNodes(lhsPreds)           
    snk match {
      case ObjVar(rgnRhs) =>
        if (getModifiers) (lhsNodes, nopHeapCheck) else {
          val rhsPreds = PtUtil.getLocalPreds(rgnRhs, hg)
          // get all CGNodes that contain a local pointing at both A0 and A1 (needed to do the required field write)
          (lhsNodes.intersect(getLPKNodes(rhsPreds)), 
           (argUse : Int, node : CGNode, rgnRhs : Set[InstanceKey]) => rhsPreds.contains(Var.makeLPK(argUse, node, hm)))
        }
      case p@PureVar(_) => (lhsNodes, nopHeapCheck)
    }  
  }
  
  // getting modifiers and producers is exactly the same except that the "may eq" check on the RHS of the edge always passes for modifers, but may not for producers
  private def getModifiersOrProducersInternal(e : PtEdge, qry : Qry, getModifiers : Boolean) : List[(CGNode, SSAInstruction)] = e match {
    // special case for array length constraints
    case ObjPtEdge(ObjVar(rgnLhs), f@InstanceFld(_), p@PureVar(_)) if Fld.isArrayLengthFld(f) => // edge A0.length -> p
      val lhsPreds = PtUtil.getLocalPreds(rgnLhs, hg)
      val lhsNodes = getLPKNodes(lhsPreds)
      lhsNodes.foldLeft (List.empty[(CGNode,SSAInstruction)]) ((lst, node) => {
        val ir = node.getIR()
        if (ir != null) {
          val tbl = ir.getSymbolTable()
          // edge can be produced by x.f := y where x -> A0 and y -> A1
          IRUtil.getAllInstructions(node).foldLeft (lst) ((lst, instr) => instr match { 
            case i : SSANewInstruction if i.getNewSite().getDeclaredType().isArrayType() &&
              rgnLhs.contains(hm.getInstanceKeyForAllocation(node, i.getNewSite())) &&              
              rhsMayEqCheck(p, i.getUse(0), node, tbl, qry, nopHeapCheck, getModifiers) => (node, i) :: lst              
              //pureMayEqCheck(i.getUse(0), p, tbl, qry) => (node, i) :: lst
            case _ => lst
          })
        } else lst
      }) 
      
    case e@ObjPtEdge(ObjVar(rgnLhs), InstanceFld(fld), snk) => // edge A0.f -> A1
      val lhsPreds = PtUtil.getLocalPreds(rgnLhs, hg)
      val (producerOrModifierNodes, heapCheck) = getProducerOrModifierNodesAndHeapCheck(rgnLhs, snk, getModifiers)
      // final instance fields can only be written in constructors
      producerOrModifierNodes.foldLeft (List.empty[(CGNode,SSAInstruction)]) ((lst, node) => if (!fld.isFinal() || node.getMethod().isInit()) { 
        val ir = node.getIR()
        if (ir != null) {
          val tbl = ir.getSymbolTable()
          // edge can be produced by x.f := y where x -> A0 and y -> A1
          IRUtil.getAllInstructions(node).foldLeft (lst) ((lst, instr) => instr match {        
            case i : SSAPutInstruction if (cha.resolveField(i.getDeclaredField()) == fld && 
              lhsPreds.contains(Var.makeLPK(i.getRef(), node, hm)) &&
              rhsMayEqCheck(snk, i.getVal(), node, tbl, qry, heapCheck, getModifiers)) => (node, i) :: lst
            case _ => lst
          })
        } else lst
      } else lst)
             
    case StaticPtEdge(_, f@StaticFld(key), snk) => // edge C.f -> A
      val fld = f.iFld
      val classInit = CGNodeUtil.getClassInitializerFor(fld.getDeclaringClass(), cg)       
      val (producerOrModifierNodes, heapCheck) = snk match {
        case ObjVar(rgnRhs) => 
          val rhsPreds = {
            val preds = PtUtil.getLocalPreds(rgnRhs, hg)
            // for now, unsoundly (but plausibly) assuming that libraries don't write to application static fields
            if (!ClassUtil.isLibrary(fld)) preds.filterNot(k => ClassUtil.isLibrary(k.getNode())) else preds
          }
          val nodes = // final static fields can only be written in class inits 
            if (fld.isFinal()) classInit match {
              case Some(classInit) => List(classInit)
              case None => sys.error("Class initializer should exist for final static field!")
            } else { 
              if (getModifiers) cg.toSet // since we're node allowed to reason about the RHS, need to consider *all* nodes in the callgraph
              else getLPKNodes(rhsPreds) 
            }          
          (nodes, if (getModifiers) nopHeapCheck else (argUse : Int, node : CGNode, rgnRhs : Set[InstanceKey]) => rhsPreds.contains(Var.makeLPK(argUse, node, hm)))
        case p@PureVar(_) => // this case is annoying because the write could be in *any* CGNode. find the ones with at least one candidate write 
          (cg.iterator().foldLeft (List.empty[CGNode]) ((lst, node) => {
            val ir = node.getIR() 
            if (ir != null && 
              IRUtil.getAllInstructions(node).exists(i => i match {
                case i : SSAPutInstruction if i.isStatic() && cha.resolveField(i.getDeclaredField()) == fld => true
                case _ => false
              })) node :: lst
            else lst
          }), nopHeapCheck)            
      }
      val instrs = 
        if (classInit.isDefined) List.empty[(CGNode,SSAInstruction)]
        // deal with nasty case where WALA does not emit a class initializer : generate our own default value instruction
        else List((WALACFGUtil.getFakeWorldClinitNode(cg), IRUtil.getDefaultValueAssignmentForStaticField(key)))
      producerOrModifierNodes.foldLeft (instrs) ((lst, node) => {
        val ir = node.getIR()
        if (ir != null) {
          val tbl = ir.getSymbolTable() 
          // edge can by produced by C.f = y where y -> A
          IRUtil.getAllInstructions(node).foldLeft (lst) ((lst, instr) => instr match { 
            case i : SSAPutInstruction if (i.isStatic() && cha.resolveField(i.getDeclaredField()) == fld && 
              rhsMayEqCheck(snk, i.getVal(), node, tbl, qry, heapCheck, getModifiers)) => (node, i) :: lst
            case _ => lst
          })
        } else lst
      })
        
    case ArrayPtEdge(ObjVar(rgnLhs), fld, snk) => // A0[i] = f
      val lhsPreds = PtUtil.getLocalPreds(rgnLhs, hg)
      val (producerOrModifierNodes, heapCheck) = getProducerOrModifierNodesAndHeapCheck(rgnLhs, snk, getModifiers)
      producerOrModifierNodes.foldLeft (List.empty[(CGNode,SSAInstruction)]) ((lst, node) => {
        val ir = node.getIR()
        if (ir != null) {
          val tbl = ir.getSymbolTable()
          // edge can be produced by x[i] := y where x -> A0 and y -> A1
          IRUtil.getAllInstructions(node).foldLeft (lst) ((lst, instr) => instr match {
            case i : SSAArrayStoreInstruction if lhsPreds.contains(Var.makeLPK(i.getArrayRef(), node, hm)) &&
              rhsMayEqCheck(snk, i.getValue(), node, tbl, qry, heapCheck, getModifiers) &&
              arrayIndicesPossiblyEqual(i.getIndex, fld, tbl, qry) => (node, i) :: lst
            case _ => lst
          })
        } else lst
      })      
    case LocalPtEdge(LocalVar(lhs), snk) =>                          
      val node = lhs.getNode()      
      // TODO : use query call stack information here if applicable
      if (lhs.isParameter()) cg.getPredNodes(node).foldLeft (List.empty[(CGNode, SSAInstruction)]) ((lst, caller) => {
        val sites = cg.getPossibleSites(caller, node).toSet
        val ir = caller.getIR()
        if (ir != null) {
          val tbl = caller.getIR().getSymbolTable()
          IRUtil.getAllInstructions(caller).foldLeft (lst) ((lst, instr) => instr match {
            case i : SSAInvokeInstruction if (sites.contains(i.getCallSite()) &&  
              rhsMayEqCheck(snk, i.getUse(lhs.getValueNumber() - 1), caller, tbl, qry, 
                  (argNum, caller, rgnRhs) => PtUtil.contains(Var.makeLPK(argNum, caller, hm), rgnRhs, hg), getModifiers)) => (caller, i) :: lst           
            case _ => lst
          })
        } else lst
      }) else {
        val ir = node.getIR()   
        if (ir != null) {
          val tbl = ir.getSymbolTable()
          assert(!tbl.isConstant(lhs.getValueNumber()), "Have edge " + e + " but " + lhs + " is a constant.")
          IRUtil.getAllInstructions(node).collect({ // non-param case
            // ... x := new_A (), or 
            case i : SSANewInstruction => if (lhsesEq(lhs, i) && { snk match {
              case ObjVar(rgnRhs) => getModifiers || rgnRhs.contains(hm.getInstanceKeyForAllocation(node, i.getNewSite()))
              case p@PureVar(_) =>
                try {
                  qry.checkTmpPureConstraint(Pure.makeNeNullConstraint(p))
                } catch {
                  case e : UnknownSMTResult => true
                }
             }}) Some(node, i) else None            
            // ... x := y.f where y.f -> A or x := Class.f, or 
            case i : SSAGetInstruction =>
              cha.resolveField(i.getDeclaredField) match {
                case null => None
                case fld =>
                  if (lhsesEq(lhs, i) && (i.isStatic() ||
                        rhsMayEqCheck(snk, i.getRef, node, tbl, qry,
                                      (argUse, node, rgnRhs) => PtUtil.contains(Var.makeLPK(argUse, node, hm), fld, rgnRhs, hg),
                                      getModifiers)))
                    Some(node, i)
                  else None
              }
            // ... x := y[i] where y[i] -> A
            case i : SSAArrayLoadInstruction => if (lhsesEq(lhs, i) && 
                rhsMayEqCheck(snk, i.getArrayRef(), node, tbl, qry, 
                 (argUse, node, rgnRhs) => PtUtil.arrContains(Var.makeLPK(argUse, node, hm), rgnRhs, hg), getModifiers)) Some(node, i) else None 
            // ... x := phi(y_0...y_n) where y_n -> A
            case i : SSAPhiInstruction =>
              if (lhsesEq(lhs, i) && 
              (0 until i.getNumberOfUses()).exists(use =>
                rhsMayEqCheck(snk, i.getUse(use), node, tbl, qry, 
                  (argUse, node, rgnRhs) => PtUtil.contains(Var.makeLPK(argUse, node, hm), rgnRhs, hg), getModifiers))) Some(node, i) else None
            case i : SSAInstruction if (i.hasDef() && lhsesEq(lhs, i)) => Some(node, i) // catch-all for other instructions
          }).flatten
        } else Nil
      }

    case LocalPtEdge(ReturnVar(lhs), snk) =>
      val node = lhs.getNode()
      val ir = node.getIR()
      if (ir != null) {
        val tbl = ir.getSymbolTable()      
        IRUtil.getAllInstructions(node).collect({
          case i : SSAReturnInstruction => if (rhsMayEqCheck(snk, i.getResult(), node, tbl, qry, 
              (argUse, node, rgnRhs) => PtUtil.contains(Var.makeRVK(node, hm), rgnRhs, hg), getModifiers)) Some(node, i) else None 
        }).flatten
      } else Nil
  }
  
}