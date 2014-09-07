package edu.colorado.thresher.core;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSACFG.ExceptionHandlerBasicBlock;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSAThrowInstruction;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.graph.Acyclic;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.graph.dominators.Dominators;
import com.ibm.wala.util.graph.traverse.BFSIterator;
import com.ibm.wala.util.graph.traverse.BFSPathFinder;
import com.ibm.wala.util.intset.IBinaryNaturalRelation;
import com.ibm.wala.util.intset.IntIterator;
import com.ibm.wala.util.intset.IntPair;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.MutableIntSet;
import com.ibm.wala.util.intset.MutableSparseIntSet;

/**
 * utility class for asking various common questions about WALA CFG's
 * 
 * @author sam
 * 
 */
public class WALACFGUtil {

  // optimization: map from IR to loop headers for that IR to save us from
  // recomputing loop heads
  private static final Map<IR, MutableIntSet> loopHeadersCache = HashMapFactory.make();
  // optimization: map from IR to dominators for that IR to save us from
  // recomputing dominators
  private static final Map<IR, Dominators<ISSABasicBlock>> dominatorsCache = HashMapFactory.make();
  // optimization: map from (IR, loop head) to blocks contained in that loop
  // head
  private static final Map<Pair<IR, SSACFG.BasicBlock>, Set<ISSABasicBlock>> loopBodyCache = HashMapFactory.make();

  // CGNode for class initializers
  private static CGNode fakeWorldClinit = null;

  /**
   * empty the loop header and dominators cache - should do before analyzing a
   * new program
   */
  public static void clearCaches() {
    loopHeadersCache.clear();
    dominatorsCache.clear();
    fakeWorldClinit = null;
  }

  /**
   * @param instr
   *          - suspected constructor
   * @return true if instr is a constructor, false otherwise
   */
  public static boolean isConstructor(SSAInvokeInstruction instr) {
    return instr.isSpecial() && instr.toString().contains("<init>");
  }

  public static boolean isClassInit(SSAInvokeInstruction instr) {
    return instr.isStatic() && instr.toString().contains("<clinit>");
  }

  /**
   * @param suspected
   *          loop head
   * @param IR
   *          for block containing suspected loop head
   * @return true if suspsectedHead is a loop head, false otherwise
   */
  public static boolean isLoopHead(SSACFG.BasicBlock suspectedHead, IR ir) {
    MutableIntSet loopHeaders = getLoopHeaders(ir);
    SSACFG cfg = ir.getControlFlowGraph();
    //Util.Print("Is " + suspectedHead + " a loop head in " + ir + " " + loopHeaders.contains(cfg.getNumber(suspectedHead)));
    return loopHeaders.contains(cfg.getNumber(suspectedHead));
  }

  /**
   * get loop headers from cache or create them
   */
  public static MutableIntSet getLoopHeaders(IR ir) {
    MutableIntSet loopHeaders = loopHeadersCache.get(ir);
    final SSACFG cfg = ir.getControlFlowGraph();
    if (loopHeaders == null) {
      loopHeaders = MutableSparseIntSet.makeEmpty();
      final IBinaryNaturalRelation backEdges = Acyclic.computeBackEdges(cfg, cfg.entry());
      final Dominators<ISSABasicBlock> domInfo = getDominators(ir);

      for (IntPair p : backEdges) {
        final ISSABasicBlock dst = cfg.getNode(p.getY());
        if (dst instanceof ExceptionHandlerBasicBlock) continue;
        final ISSABasicBlock src = cfg.getNode(p.getX());
        if (domInfo.isDominatedBy(src, dst)) {
            loopHeaders.add(p.getY());
        }
      }
      loopHeadersCache.put(ir, loopHeaders);
    }
    return loopHeaders;
  }

  static boolean isDominatedBy(SSACFG.BasicBlock dominated, SSACFG.BasicBlock master, IR ir) {
    Dominators<ISSABasicBlock> domInfo = getDominators(ir);
    // return domInfo.isDominatedBy(dominated, master);
    boolean result = domInfo.isDominatedBy(dominated, master);
    return result;
  }

  /**
   * get dominators from cache or create them
   */
  static Dominators<ISSABasicBlock> getDominators(IR ir) {
    Dominators<ISSABasicBlock> domInfo = dominatorsCache.get(ir);
    if (domInfo == null) {
      final SSACFG cfg = ir.getControlFlowGraph();
      domInfo = Dominators.make(cfg, cfg.entry());
      dominatorsCache.put(ir, domInfo);
    }
    return domInfo;
  }

  /**
   * is suspectedEscapeBlock inside of the loop, or BEFORE it? THIS SHOULD NOT
   * BE USED TO ASK IF A BLOCK IS AFTER THE LOOP
   * 
   * @param loopHead
   *          - head of loop whose escape block we are looking for
   * @return - true if escape block, false otherwise
   */
  public static boolean isLoopEscapeBlock(SSACFG.BasicBlock suspectedEscapeBlock, SSACFG.BasicBlock loopHead, IR ir) {
    //Dominators<ISSABasicBlock> domInfo = getDominators(ir);
    // TODO: figure out which of these doesn't hold in Enumerator example.  
    if (!isInLoopBody(suspectedEscapeBlock, loopHead, ir) && // we have an
                                                             // escape block if
                                                             // it's not in the
                                                             // loop...
        // and it transitions directly to the loop head
        (isDirectlyReachableFrom(loopHead, suspectedEscapeBlock, ir.getControlFlowGraph()) ||  
         isConditionalBlockThatTransitionsTo(suspectedEscapeBlock, loopHead, ir.getControlFlowGraph()))) {
      
        // really, we want "reachable without back edge" 
      
        // if (b) { while (e) s1 }
      
        // dominator relationship doesn't hold for code like
        // if (e) s1 else s2; while (e) s3. s1 and s2 are both loop escape blocks
        //domInfo.isDominatedBy(loopHead, suspectedEscapeBlock)) { // ... and it
                                                                 // dominates
                                                                 // the loop
                                                                 // head
      //Thread.dumpStack();
      //Util.Assert(isDirectlyReachableFrom(loopHead, suspectedEscapeBlock, ir.getControlFlowGraph()), "dif result! " + ir);
      return true;
    }
    
    return false;
  }
  
  public static ISSABasicBlock findEscapeBlockForDoWhileLoop(SSACFG.BasicBlock loopHead, IR ir) {
    SSACFG cfg = ir.getControlFlowGraph();
    Set<ISSABasicBlock> body = getLoopBodyBlocks(loopHead, ir);
    // there should be one block in the loop body that has a predecessor outside of the loop. this
    // predecessor will be our escape block
    for (ISSABasicBlock bodyBlock : body) {
      for (ISSABasicBlock pred : cfg.getNormalPredecessors(bodyBlock)) {
        if (!body.contains(pred)) return pred;
      }
    }
    //Util.Unimp("couldn't find escape block for do..while loop headed by " + loopHead + " " + 
      //  ir + " blocks " + Util.printCollection(body));
    return null;
  }

  /**
   * @return - true if suspectedLoopBodyBlock is in the body of *any* loop,
   *         false otherwise
   */
  public static boolean isInLoopBody(SSACFG.BasicBlock suspectedLoopBodyBlock, IR ir) {
    //return getLoopHeadForBlock(suspectedLoopBodyBlock, ir) != null;
    final SSACFG cfg = ir.getControlFlowGraph();
    MutableIntSet headers = getLoopHeaders(ir);
    final IntIterator iter = headers.intIterator();
    while (iter.hasNext()) {
      if (getLoopBodyBlocks(cfg.getBasicBlock(iter.next()), ir).contains(suspectedLoopBodyBlock)) return true;
    }
    return false;
  }

  /**
   * @return - head of closest loop containing suspectedLoopBodyBlock if there is one, null otherwise
   * that is, if the block B is in a nested loop while (e0) { while (e1) { B } }, this will return the loop
   * head associated with e1 
   */
  //public static SSACFG.BasicBlock getLoopHeadForBlock(SSACFG.BasicBlock suspectedLoopBodyBlock, IR ir) {
  public static SSACFG.BasicBlock getLoopHeadForBlock(SSACFG.BasicBlock suspectedLoopBodyBlock, IR ir) {
    final Dominators<ISSABasicBlock> domInfo = getDominators(ir);
    final MutableIntSet loopHeaders = getLoopHeaders(ir);
    final SSACFG cfg = ir.getControlFlowGraph();
    final IntIterator iter = loopHeaders.intIterator();
    Set<ISSABasicBlock> loopHeadBlocks = HashSetFactory.make();
    //List<ISSABasicBlock> loopHeadBlocks = new ArrayList<ISSABasicBlock>();
    while (iter.hasNext()) {
      SSACFG.BasicBlock loopHeadBlock = cfg.getBasicBlock(iter.next());
      //if (!(loopHeadBlock.getLastInstruction() instanceof SSAConditionalBranchInstruction)) {
        //Util.Debug("no conditional--continuing..");
        //continue;
      //}
      // a block may B is in a loop by if it is dominated by the loop head...
      if (domInfo.isDominatedBy(suspectedLoopBodyBlock, loopHeadBlock) && 
          // ...and the loop head is reachable from B
          isReachableFrom(suspectedLoopBodyBlock, loopHeadBlock, ir)) {
        loopHeadBlocks.add(loopHeadBlock);
      }
      
      // special case for do...while
      // a block may B is in a do...while loop by if it dominates the loop head...
      if (domInfo.isDominatedBy(loopHeadBlock, suspectedLoopBodyBlock) && 
          // ...and the B is reachable from the loop head
          isReachableFrom(loopHeadBlock, suspectedLoopBodyBlock, ir)) {
        loopHeadBlocks.add(loopHeadBlock);
      }
      
    }
    if (loopHeadBlocks.size() == 0) return null;
    else if (loopHeadBlocks.size() == 1) return (SSACFG.BasicBlock) loopHeadBlocks.iterator().next();
    // get the block lowest in the dominator hierarchy--that's the one we want
    //Collections.sort(loopHeadBlocks, new DomComparator(domInfo));
    //Util.Print("loop head block for ")
    //return (SSACFG.BasicBlock) loopHeadBlocks.get(0);
    Graph<ISSABasicBlock> g = cfg;
    // now, we have ths list of loop heads for loops that enclose this block.
    // execute forward from the block and see which loop head is the first 
    // one we hit; this one will be the enclosing loop head
    // TODO: this could go awry with break statements...
    BFSIterator<ISSABasicBlock> blkIter = 
        new BFSIterator<ISSABasicBlock>(g, (ISSABasicBlock) suspectedLoopBodyBlock);
    while (blkIter.hasNext()) {
      ISSABasicBlock next = blkIter.next();
      if (loopHeadBlocks.contains(next)) return (SSACFG.BasicBlock) next; // found it
    }
    //Util.Assert(false, "couldn't find loop head for " + suspectedLoopBodyBlock);
    return null;
  }
  
  private static class DomComparator implements Comparator<ISSABasicBlock> {
    private final Dominators<ISSABasicBlock> domInfo;
    private DomComparator(Dominators<ISSABasicBlock> domInfo) {
      this.domInfo = domInfo;
    }
    
    @Override
    public int compare(ISSABasicBlock loopHead0, ISSABasicBlock loopHead1) {
      // loopHead0 < loopHead1 if loopHead1 dominates loopHead0
      if (domInfo.isDominatedBy(loopHead0, loopHead1)) return -1;
      else if (domInfo.isDominatedBy(loopHead1, loopHead0)) return 1;
      // otherwise, they're equal
      return 0;
    }
  }

  /**
   * get the block that precedes a loop
   * 
   * @param loopHead
   * @param ir
   * @return
   */
  // TODO: doesn't work for nested loops
  public static SSACFG.BasicBlock getEscapeBlockForLoop(SSACFG.BasicBlock loopHead, IR ir) {
    Set<ISSABasicBlock> body = getLoopBodyBlocks(loopHead, ir);
    SSACFG cfg = ir.getControlFlowGraph();
    for (ISSABasicBlock blk : body) {
      Iterator<ISSABasicBlock> preds = cfg.getPredNodes(blk);
      while (preds.hasNext()) {
        ISSABasicBlock next = preds.next();
        if (!body.contains(next)) {
          return (SSACFG.BasicBlock) next;
        }
      }
    }
    
    // else, possibly nested loop. find the loop head that dominates this one 
    
    //Util.Unimp("couldn't find escape block for loopHead " + loopHead);
    return null;
  }

  public static boolean isExplicitlyInfiniteLoop(SSACFG.BasicBlock loopHead, IR ir) {
    Set<ISSABasicBlock> body = getLoopBodyBlocks(loopHead, ir);
    SSACFG cfg = ir.getControlFlowGraph();
    for (ISSABasicBlock blk : body) {
      Iterator<ISSABasicBlock> succs = cfg.getSuccNodes(blk);
      while (succs.hasNext()) {
        // if (body.contains(succs.next())) return true;
        if (!body.contains(succs.next()))
          return false;
      }
    }
    // return false;
    return true;
  }
  
  public static Set<ISSABasicBlock> getLoopBodyBlocks(int loopHead, IR ir) {
    return getLoopBodyBlocks(ir.getControlFlowGraph().getNode(loopHead), ir);
  }
  
  public static Set<ISSABasicBlock> getLoopBodyBlocks(ISSABasicBlock loopHead, IR ir) {
    return getLoopBodyBlocks((SSACFG.BasicBlock) loopHead, ir);
  }
  
  public static Set<ISSABasicBlock> getBreaks(final ISSABasicBlock loopHead, IR ir) {
    SSACFG cfg = ir.getControlFlowGraph();
    Set<ISSABasicBlock> bodyBlocks = getLoopBodyBlocks(loopHead, ir);
    Set<ISSABasicBlock> breaks = HashSetFactory.make();
    for (ISSABasicBlock bodyBlock : bodyBlocks) {
      Collection<ISSABasicBlock> succs = cfg.getNormalSuccessors(bodyBlock);
      if (succs.size() == 1 && !bodyBlocks.contains(succs.iterator().next())) {
        breaks.add(bodyBlock);
      }
    }
    return breaks;
  }
  
  // TODO: WRONG! does not capture break blocks... we never get to them by following the back edge
  /**
   * @return - loop body blocks in the loop *owned* by loopHead
   * that is, for the program while (e0) { s0; while (e1) { s1; } s2; }, getting the loop body
   * blocks for the loop head corresponding to e0 will yield the entire program; getting the 
   * loop body blocks for the loop head corresponding to e1 will yield while (e) { s1; }.
   */ 
  private static Set<ISSABasicBlock> getLoopBodyBlocks(final SSACFG.BasicBlock loopHead, IR ir) {
    SSACFG cfg = ir.getControlFlowGraph();
    Pair<IR, SSACFG.BasicBlock> key = Pair.make(ir, loopHead);
    Set<ISSABasicBlock> loopBody = loopBodyCache.get(key);
    
    if (loopBody == null) {
      //if (Options.DEBUG) Util.Debug("getting loop body blocks for " + loopHead + " in " + ir);
      // loop head is the sink of a back edge, so just follow predecessors from the back edge
      // until we hit the loop head again
      List<ISSABasicBlock> toExplore = new LinkedList<ISSABasicBlock>();
      Dominators<ISSABasicBlock> domInfo = getDominators(ir);
      for (ISSABasicBlock blk : cfg.getNormalPredecessors(loopHead)) {
        /*
        // if the block dominates the loop head it's not part of the back edge
        if (!domInfo.isDominatedBy(loopHead, blk)) toExplore.add(blk);
        */
        // if the block dominates the loop head, it's not part of the back edge
        // if the block does not dominate the loop head, it's not part of the back edge
        if (!domInfo.isDominatedBy(loopHead, blk) &&
            domInfo.isDominatedBy(blk, loopHead))  {
          toExplore.add(blk);
        }

      }
      loopBody = HashSetFactory.make();
      while (!toExplore.isEmpty()) {
        ISSABasicBlock blk = toExplore.remove(0);
        if (loopBody.add(blk) && blk != loopHead) {
          toExplore.addAll(cfg.getNormalPredecessors(blk));
        }
      }
      
      /*
      // now we have all the blocks in the loop body that are not breaks
      // walk forward from each of these blocks, adding all blocks that 
      //for (ISSABasicBlock loopBodyBlk : loopBody) {
        //Util.Assert(loopBodyBlk != loopHead);
        
      //}      
      // get blocks dominated by the "loop entry" block that are not reachable from the the "loop skip" block
      // get blocks reachable from the loop entry block that are not reachable from the loop exit block
      */
      
      //if (Options.DEBUG) Util.Debug("loop body blocks for " + loopHead + "\n: " + Util.printCollection(loopBody));
      loopBodyCache.put(key, loopBody);
    }
    
    return loopBody;
  }
  

  /*
  private static Set<ISSABasicBlock> getLoopBodyBlocks(final SSACFG.BasicBlock loopHead, IR ir) {
    Util.Pre(isLoopHead(loopHead, ir));
    Util.Debug("getting loop body blocks for " + loopHead);
    Pair<IR, SSACFG.BasicBlock> key = Pair.make(ir, loopHead);
    Set<ISSABasicBlock> loopBody = loopBodyCache.get(key);
    if (loopBody == null) {
      if (loopBodyCache.keySet() != null) Util.Debug("keys " + Util.printCollection(loopBodyCache.keySet()));
      loopBody = HashSetFactory.make();
      loopBody.add(loopHead);
      // find the forward escape block of the loopHead
      SSACFG cfg = ir.getControlFlowGraph();
      Set<ISSABasicBlock> seen = HashSetFactory.make();
      Collection<ISSABasicBlock> succs = cfg.getNormalSuccessors((ISSABasicBlock) loopHead);
      // we're in a loop setup block. keep executing until we hit the conditional split for the loop or we wrap around
      while (succs.size() < 2) { 
        ISSABasicBlock next = succs.iterator().next();
        loopHead = (SSACFG.BasicBlock) next;
        if (!seen.add(next)) {
          // this is an expliclity infinite loop, and we've wrapped back around
          // to the beginning. return seen set
          return seen;
        }
        succs = cfg.getNormalSuccessors(next);
      }
      // now we should have > 1 succ
      Util.Assert(succs.size() > 1, "need to be looking a loop escape block! instead have succs of " + loopHead);
      Set<ISSABasicBlock> toExplore = HashSetFactory.make();
      for (ISSABasicBlock succ : succs) {
        // if we can't reach the loop head from this block, it's an 
        // escape block and shouldn't be added. however, we will accidentally
        // add escape blocks if they lead into an enclosing outer loop. this
        // is dealt with later--we do not add the succs of a blk to the toExplore
        // set if it has a different loop head than the current block
        if (isReachableFrom((SSACFG.BasicBlock) succ, loopHead, ir)) {
          toExplore.add(succ);
        }
      }

      Dominators<ISSABasicBlock> domInfo = getDominators(ir);
            
      while (!toExplore.isEmpty()) {
        ISSABasicBlock blk = toExplore.iterator().next();
        toExplore.remove(blk);
        // do nested loop check
        SSACFG.BasicBlock loopHeadForBlock = getLoopHeadForBlock((SSACFG.BasicBlock) blk, ir);
        if (loopHeadForBlock != loopHead && // if this block has a different loop head... 
            domInfo.isDominatedBy(loopHead, loopHeadForBlock) && // ...and this block's loop head dominates ours
            blk != loopHeadForBlock) { // and this block is not itself a loop head (special case for do...while)
          // our loop is the inner of the two loops; we only want to compute i's loop body blocks, not those of its parent
          if (Options.DEBUG) Util.Debug("skipping " + blk + " because " + loopHeadForBlock + " dominates " + loopHead);
          continue;
        }
       
        if (!loopBody.add(blk)) continue;
        SSAInstruction lastInstr = blk.getLastInstruction();
        // if this block ends in a return, don't execute its successors
        if (lastInstr instanceof SSAReturnInstruction) continue;
        succs = cfg.getNormalSuccessors(blk);
        // check for break statements; don't want to execute successors if this 
        // block ends in a break
        if (lastInstr instanceof SSAGotoInstruction) { 
          // breaks are goto's that send us outside of the loop                                                       
          // if we can't get to the loop head from this goto, it's a break
          if (succs.size() == 1 && !isReachableFrom((SSACFG.BasicBlock) blk, loopHead, ir)) {
            Util.Debug("skipping break blk " + blk);
            continue;
          }
        }
        for (ISSABasicBlock succ : succs) {
          // if we can get fromm this block to the loop head
          if (isReachableFrom((SSACFG.BasicBlock) succ, loopHead, ir)) {
            toExplore.add(succ);
          }
        }
      }
      if (Options.DEBUG) Util.Debug("loop body blocks for " + loopHead + "\n: " + Util.printCollection(loopBody));
      loopBodyCache.put(key, loopBody);
    }
    return loopBody;
  }
  */

  /**
   * @return - true if suspectedLoopBodyBlock is in the body of loop dominated
   *         by loopHead, false otherwise
   */
  public static boolean isInLoopBody(SSACFG.BasicBlock suspectedLoopBodyBlock, SSACFG.BasicBlock loopHead, IR ir) {
    Set<ISSABasicBlock> loopBodyBlocks = getLoopBodyBlocks(loopHead, ir);
    // return loopBodyBlocks.contains(suspectedLoopBodyBlock);
    boolean result = loopBodyBlocks.contains(suspectedLoopBodyBlock);
    // Util.Debug(suspectedLoopBodyBlock + " in loop body headed by " + loopHead
    // + "? " + result);
    return result;
  }

  /**
   * @param loopHead
   *          - the head of the loop whose instructions we want
   * @param ir
   *          - IR for the method containing the loop
   * @return - set of all instructions contained in the loop
   */
  public static Set<SSAInstruction> getInstructionsInLoop(SSACFG.BasicBlock loopHead, IR ir) {
    Set<SSAInstruction> instrs = HashSetFactory.make();

    Set<ISSABasicBlock> loopBodyBlocks = getLoopBodyBlocks(loopHead, ir);
    for (ISSABasicBlock blk : loopBodyBlocks) {
      instrs.addAll(((SSACFG.BasicBlock) blk).getAllInstructions());
    }
    return instrs;
  }

  public static Set<CGNode> getCallTargetsInLoop(SSACFG.BasicBlock loopHead, CGNode loopNode, CallGraph cg) {
    IR ir = loopNode.getIR();
    Set<SSAInstruction> loopInstrs = getInstructionsInLoop(loopHead, ir);
    Set<CGNode> possibleTargets = HashSetFactory.make();
    for (SSAInstruction instr : loopInstrs) {
      if (instr instanceof SSAInvokeInstruction) {
        SSAInvokeInstruction call = (SSAInvokeInstruction) instr;
        possibleTargets.addAll(cg.getPossibleTargets(loopNode, call.getCallSite()));
      }
    }
    return possibleTargets;
  }
  
  // TODO: merge this with previous function
  public static Set<CGNode> getCallTargetsInBlocks(Set<ISSABasicBlock> blks, CGNode blkNode, CallGraph cg) {
    Set<CGNode> callees = HashSetFactory.make();
    for (ISSABasicBlock blk : blks) {
      if (blk.getLastInstructionIndex() < 0) continue;
      SSAInstruction instr = blk.getLastInstruction();
      if (instr != null && instr instanceof SSAInvokeInstruction) {
        SSAInvokeInstruction invoke = (SSAInvokeInstruction) instr;
        callees.addAll(cg.getPossibleTargets(blkNode, invoke.getCallSite()));
      }
    }
    return callees;
  }

  public static boolean isDirectlyReachableFromLoopHead(SSACFG.BasicBlock dstBlk, IR ir) {
    MutableIntSet headers = getLoopHeaders(ir);
    SSACFG cfg = ir.getControlFlowGraph();
    for (IntIterator iter = headers.intIterator(); iter.hasNext();) {
      SSACFG.BasicBlock loopHead = cfg.getBasicBlock(iter.next());
      //if (isDirectlyReachableFrom(loopHead, dstBlk, cfg)) {
      if (isDirectlyReachableFrom(dstBlk, loopHead, cfg)) {
        return true;
      }
    }
    return false; 
  }
  
  /**
   * @param srcBlk
   *          - block to search forward from
   * @param dstBlk
   *          - block we are looking for
   * @param ir
   *          - IR of method containing blocks
   * @return - true if dstBlk is reachable from srcBlk, false otherwise
   */
  public static boolean isReachableFrom(SSACFG.BasicBlock srcBlk, SSACFG.BasicBlock dstBlk, IR ir) {
    final SSACFG cfg = ir.getControlFlowGraph();
    // TODO: make more efficient; LinkedList allows duplicate blocks to be added
    final LinkedList<ISSABasicBlock> toExplore = new LinkedList<ISSABasicBlock>();
    toExplore.addAll(cfg.getNormalSuccessors(srcBlk));
    final Set<SSACFG.BasicBlock> loopHeadsSeen = HashSetFactory.make();
    while (!toExplore.isEmpty()) {
      SSACFG.BasicBlock blk = (SSACFG.BasicBlock) toExplore.remove();
      if (blk.equals(dstBlk)) {
        return true;
      } else if (!isLoopHead(blk, ir) || loopHeadsSeen.add(blk)) { // avoid
                                                                 // infinite
                                                                 // loops
        toExplore.addAll(cfg.getNormalSuccessors(blk));
      }
    }
    return false;
  }

  public static CGNode getClassInitializerFor(IClass clazz, CallGraph callGraph) {
    IMethod classInit = clazz.getClassInitializer();
    if (classInit == null) return null;
    Set<CGNode> classInits = callGraph.getNodes(classInit.getReference());
    return classInits.iterator().next();
  }

  /**
   * find and return fakeWorldClinitNode. this seems unnecessarily hard to do.
   * 
   * @param cg
   * @return
   */
  public static CGNode getFakeWorldClinitNode(CallGraph cg) {
    // find fakeWorldClinit node (class initializers)
    if (fakeWorldClinit == null) {
      Iterator<CGNode> iter = cg.iterator();
      while (iter.hasNext()) {
        CGNode node = iter.next();
        if (node.getMethod().toString().equals("synthetic < Primordial, Lcom/ibm/wala/FakeRootClass, fakeWorldClinit()V >")) {
          fakeWorldClinit = node;
        }
        /*
         * // note: this didn't work... CallSiteReference ref = iter.next();
         * System.err.println(ref.getDeclaredTarget().toString()); if
         * (ref.getDeclaredTarget().toString().equals(
         * "< Primordial, Lcom/ibm/wala/FakeRootClass, fakeWorldClinit()V >")) {
         * fakeWorldClinit =
         * cg.getNodes(ref.getDeclaredTarget()).iterator().next(); }
         */
      }
    }
    return fakeWorldClinit;
  }

  public static boolean isFakeWorldClinit(CGNode node, CallGraph cg) {
    return isFakeWorldClinit(node.getMethod().getReference(), cg);
  }

  public static boolean isFakeWorldClinit(MethodReference method, CallGraph cg) {
    CGNode clinit = getFakeWorldClinitNode(cg);
    return method.toString().equals(clinit.getMethod().getReference().toString());
  }

  /**
   * @return index into blk corresponding to instr
   */
  public static int findInstrIndexInBlock(SSAInstruction instr, SSACFG.BasicBlock blk) {
    int index = 0;
    for (SSAInstruction blkInstr : blk.getAllInstructions()) {
      // we have to do a string comparison here because if the instr's belong to
      // IR's from different contexts they won't compare equal
      if (blkInstr.toString().equals(instr.toString()))
        return index;
      // if (blkInstr.equals(instr)) return index;
      index++;
    }
    return -1;
  }

  
  public static boolean isDirectlyReachableFrom(ISSABasicBlock dst, ISSABasicBlock src, SSACFG cfg) {
    return isDirectlyReachableFrom((SSACFG.BasicBlock) dst, (SSACFG.BasicBlock) src, cfg);
  }
  
  /**
   *
   * @return - true if @param dst is directly reachable from @param src (no branching), false otherwise
   */
  public static boolean isDirectlyReachableFrom(SSACFG.BasicBlock dst, SSACFG.BasicBlock src, SSACFG cfg) {
    Collection<ISSABasicBlock> succs = null;
    Set<SSACFG.BasicBlock> seen = HashSetFactory.make();
    do {
      if (!seen.add(src)) return false; // have looped around without seeing target
      if (src.equals(dst)) return true;
      succs = cfg.getNormalSuccessors(src);
      if (succs.isEmpty()) return false;
      src = (SSACFG.BasicBlock) succs.iterator().next();
    } while (succs.size() == 1);
    return false;
  }
  
  public static boolean isConditionalBlockThatTransitionsTo(SSACFG.BasicBlock src, SSACFG.BasicBlock dst, SSACFG cfg) {
    // if this instruction is not a conditional
    if (src.getLastInstructionIndex() != -1 && 
        (src.getLastInstruction() instanceof SSAConditionalBranchInstruction)) {
      return cfg.getNormalSuccessors(src).contains(dst);
    }
    return false;
  }
  
  /**
   * @param blk
   *          - block to begin execution from
   * @return - true if straight-line execution forward from blk definitely ends
   *         in a thrown exception; false otherwise
   */
  public static boolean endsInThrownException(SSACFG.BasicBlock blk, SSACFG cfg) {
    for (;;) {
      if (!blk.getAllInstructions().isEmpty() && blk.getLastInstruction() instanceof SSAThrowInstruction)
        return true;
      Collection<ISSABasicBlock> succs = cfg.getNormalSuccessors(blk);
      if (succs.isEmpty() || succs.size() > 1)
        return false; // either we hit the end of the proc without throwing, or
                      // the path splits
      blk = (SSACFG.BasicBlock) succs.iterator().next();
    }
  }

  /**
   * are two methods the same except for the Primordial / Application
   * classloader scope?
   */
  public static boolean equalExceptScope(MethodReference method1, MethodReference method2) {
    String methodName1 = method1.getName().toString(), methodName2 = method2.getName().toString();
    if (methodName1.equals(methodName2)) {
      return method1.getDeclaringClass().getName().toString().equals(method2.getDeclaringClass().getName().toString());
    }
    return false;
  }

  public int distanceToEntrypoint(CallGraph cg, CGNode node) {
    BFSPathFinder<CGNode> finder = new BFSPathFinder<CGNode>(cg, cg.getEntrypointNodes().iterator(), node);
    List<CGNode> lst = finder.find();
    if (lst != null)
      return lst.size();
    return -1;
  }

  public static SSAInvokeInstruction getCallInstructionFor(CGNode callee, CGNode caller) {
    MethodReference calleeMethod = callee.getMethod().getReference();
    Iterator<SSAInstruction> instrs = caller.getIR().iterateAllInstructions();
    while (instrs.hasNext()) {
      SSAInstruction instr = instrs.next();
      if (instr instanceof SSAInvokeInstruction) {
        SSAInvokeInstruction call = (SSAInvokeInstruction) instr;
        // if (call.getDeclaredTarget().equals(calleeMethod)) {
        if (equalExceptScope(call.getDeclaredTarget(), calleeMethod)) {
          return call;
        }
      }

    }
    return null;
  }
  
  public static Collection<Pair<SSAInvokeInstruction,Integer>> getCallInstructionsAndIndices(CGNode callee, CGNode caller, CallGraph cg) {
    IR callerIR = caller.getIR();
    SSAInstruction[] instrs = callerIR.getInstructions();
    Collection<Pair<SSAInvokeInstruction,Integer>> pairs = new ArrayList<Pair<SSAInvokeInstruction,Integer>>();

    for (Iterator<CallSiteReference> siteIter = cg.getPossibleSites(caller, callee); siteIter.hasNext();) {
      CallSiteReference site = siteIter.next();
      IntSet indices = callerIR.getCallInstructionIndices(site);
      for (IntIterator indexIter = indices.intIterator(); indexIter.hasNext();) {
        int callLine = indexIter.next();
        
        SSAInstruction instr = instrs[callLine];
        pairs.add(Pair.make((SSAInvokeInstruction) instr, callLine));
      }
    }
    return pairs;
  }
  
  /*
  public static SSAInvokeInstruction getCallInstructionFor(CGNode callee, CGNode caller, CallGraph cg) {
    Set<CallSiteReference> siteRefs = Util.iteratorToSet(cg.getPossibleSites(caller, callee));
    
    Iterator<SSAInstruction> instrs = caller.getIR().iterateAllInstructions();
    while (instrs.hasNext()) {
      SSAInstruction instr = instrs.next();
      if (instr instanceof SSAInvokeInstruction) {
        SSAInvokeInstruction call = (SSAInvokeInstruction) instr;
        // if (call.getDeclaredTarget().equals(calleeMethod)) {
        if (siteRefs.contains(call.getCallSite()))
          return call;
        // if (equalExceptScope(call.getDeclaredTarget(), calleeMethod)) {
        // return call;
        // }
      }

    }
    Util.Assert(false, "couldn't find call to " + callee + " in caller " + caller);
    return null;
  }
  */
  
  public static SSAConditionalBranchInstruction getInstrForLoopHead(SSACFG.BasicBlock loopHead, SSACFG cfg) {
    if (loopHead.getLastInstructionIndex() != -1) {
      SSAInstruction instr = loopHead.getLastInstruction();
      if (instr instanceof SSAConditionalBranchInstruction) return (SSAConditionalBranchInstruction) instr;
    }
    // else, have to search backwards until we find it
    // TODO: should we go forwards to?
    /*
    while (cfg.getPredNodeCount(loopHead) == 1) {
      loopHead = (SSACFG.BasicBlock) cfg.getPredNodes(loopHead).next();
      Util.Debug("blk " + loopHead);
      if (loopHead.getLastInstructionIndex() != -1) {
        SSAInstruction instr = loopHead.getLastInstruction();
        if (instr instanceof SSAConditionalBranchInstruction) return (SSAConditionalBranchInstruction) instr;
      }
    }
    */
    Collection<ISSABasicBlock> succs = cfg.getNormalSuccessors(loopHead);
    while (succs.size() == 1) {
      ISSABasicBlock succ = succs.iterator().next();
      if (succ.getLastInstructionIndex() != -1) {
        SSAInstruction instr = succ.getLastInstruction();
        if (instr instanceof SSAConditionalBranchInstruction) return (SSAConditionalBranchInstruction) instr;
      }
      succs = cfg.getNormalSuccessors(succ); // else, keep looking
    }
    
    return null;
  }
}
