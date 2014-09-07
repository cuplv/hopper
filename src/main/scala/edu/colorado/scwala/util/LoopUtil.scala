package edu.colorado.scwala.util

import scala.collection.JavaConversions.collectionAsScalaIterable
import scala.collection.JavaConversions.iterableAsScalaIterable
import scala.collection.mutable.HashMap
import com.ibm.wala.ssa.IR
import com.ibm.wala.ssa.SSACFG
import com.ibm.wala.util.graph.Acyclic
import com.ibm.wala.util.graph.dominators.Dominators
import com.ibm.wala.util.intset.IntPair
import com.ibm.wala.ssa.ISSABasicBlock
import edu.colorado.scwala.translate.WalaBlock

object LoopUtil {  
  val DEBUG = false
  
  type MSet[T] = scala.collection.mutable.Set[T]
    
  // TODO: we can cache a lot more here (loop bodies e.t.c) if performance is a problem;
  // there's certainly a lot of redundant computation right now
  val dominatorsCache = new HashMap[IR,Dominators[ISSABasicBlock]]
  val loopHeaderCache = new HashMap[IR,Set[Int]]   
  //val doLoopHeaderCache = new HashMap[IR,Set[Int]]
  val doLoopHeaderCache = new HashMap[IR,MSet[Int]]
    
  def clearCaches() : Unit = {
    dominatorsCache.clear
    loopHeaderCache.clear
    doLoopHeaderCache.clear
  }
    
  /**
   * @return the dominators for IR
   */
  def getDominators(ir : IR) : Dominators[ISSABasicBlock] = {
   def computeDominators(ir : IR) : Dominators[ISSABasicBlock] = {
    val cfg = ir.getControlFlowGraph()
      Dominators.make(cfg, cfg.entry());
    }
    dominatorsCache.getOrElseUpdate(ir, computeDominators(ir))
  }
  
  /*
  def getBackEdges(ir : IR) : Set[Int] = {
    
  }
  */
    
    /**
     * @return the set of basic block numbers that are sinks of some back edge in IR
     */
    def getLoopHeaders(ir : IR) : Set[Int] = {
      val doLoops = Util.makeSet[Int]
      def computeLoopHeaders(ir : IR) : Set[Int]= {
        val cfg = ir.getControlFlowGraph()
        val backEdges = Acyclic.computeBackEdges(cfg, cfg.entry())
        val domInfo = getDominators(ir)
        backEdges.foldLeft (Set.empty[Int]) ((s : Set[Int], p : IntPair) => {
          val (src, dst) = (cfg.getNode(p.getX()), cfg.getNode(p.getY()))
          if (DEBUG) println("back edge " + src + " -> " + dst)    
          if (!dst.isCatchBlock() && domInfo.isDominatedBy(src, dst)) {
            if (CFGUtil.endsWithConditionalInstr(src) && {
                CFGUtil.getFallThroughBlocks(dst, cfg, true).find(blk => CFGUtil.endsWithConditionalInstr(blk)) match {
              case Some(condBlk) =>
                if (DEBUG) println("checking for do with cond " + condBlk)
                if (condBlk == src) true 
                else if (condBlk == dst) false
                else {
                  val succs = CFGUtil.getSuccessors(condBlk, cfg)
                  assert (succs.size == 2)
                  if (DEBUG) println("succs " + succs(0) + " and " + succs(1))
                  // if either successor has a number greater than the tail, this is a while loop
                  // TODO: what about breaks? pretty sure this will report do{ loops whose first conditional is a break as while loop
                  //succs(0).getNumber() < src.getNumber() && succs(1).getNumber() < src.getNumber() 
                  succs(0).getNumber() <= src.getNumber() && succs(1).getNumber() <= src.getNumber() 
                  // if one of the successors of the condBlk dominates the loop tail, but the other does not, then
                  // this is a regular loop; otherwise, this is a do loop
                  // TODO: breaks and returns in the loop mess this up. ugh. hopefully the hack-y numbers check will fix this
                  //if either of the succs has a number greater than the number of the tail, this is a regular loop
                  //succs(0).getNumber() <= dst.getNumber() && succs(1).getNumber() <= dst.getNumber() && {
                    //val (dom1, dom2) = (domInfo.isDominatedBy(src, succs(0)), domInfo.isDominatedBy(src, succs(1)))
                    //if (DEBUG) println("condblk " + condBlk + " succs(0) " + succs(0) + " succs(1) " + succs(1) + " dom1? " + dom1 + " dom2? " + dom2)
                    //assert (dom1 || dom2)
                    //!(dom1 ^ dom2)
                  //}
                }
              case None => 
                if (DEBUG) println("no condBlk; found do ")
                true
            }}) {
              //if (DEBUG) println("got do loop " + p.getY())
              //println("got do loop " + p.getY())
              doLoops.add(p.getY())
            }
            /*
            if (CFGUtil.endsWithConditionalInstr(src) && {
                CFGUtil.getFallThroughBlocks(dst, cfg).find(blk => CFGUtil.endsWithConditionalInstr(blk)) match {
              case Some(condBlk) =>
                if (condBlk == src) { println(src + " falls through to do conditional; found do"); true }
                else {
                  val succs = CFGUtil.getSuccessors(condBlk, cfg)
                  assert (succs.size == 2)
                  // if one of the successors of the condBlk dominates the loop tail, but the other does not, then
                  // this is a regular loop; otherwise, this is a do loop
                  // TODO: breaks and returns in the loop mess this up. ugh. hopefully the hack-y numbers check will fix this
                  //if either of the succs has a number greater than the number of the tail, this is a regular loop
                  //succs(0).getNumber() <= dst.getNumber() && succs(1).getNumber() <= dst.getNumber() && {
                    val (dom1, dom2) = (domInfo.isDominatedBy(src, succs(0)), domInfo.isDominatedBy(src, succs(1)))
                    if (DEBUG) println("condblk " + condBlk + " succs(0) " + succs(0) + " succs(1) " + succs(1) + " dom1? " + dom1 + " dom2? " + dom2)
                    //assert (dom1 || dom2)
                    !(dom1 ^ dom2)
                  //}
                }
              case None => true
            }}) {
               if (DEBUG) println("got do loop " + p.getY())
               doLoops.add(p.getY())
            }
            */  
            

            /*
            // TODO: do something better here. second boolean is especially hack-tastic. 
            if (CFGUtil.endsWithConditionalInstr(src) && (!CFGUtil.fallsThroughToConditional(dst, cfg) || 
                CFGUtil.getFallThroughBlocks(src, cfg).contains(src)) && {
              // get the successor of the conditional that is not part of the back edge
              val otherSucc = CFGUtil.getSuccessors(src, cfg).filterNot(blk => blk == dst)
              assert (otherSucc.size == 1)              
              // if we can't get back to the loop head while ignoring the back edge starting at src and ignoring back edges of outer loops
              // then this is a do loop
              !(CFGUtil.getSuccsWhile(otherSucc.head, cfg, 
                  blk => !backEdges.anyRelated(blk.getNumber()) || blk == dst || {
                    println("getting back edge with src " + blk)
                    // ignore back edges of outer loops
                    val intIter = backEdges.getRelated(blk.getNumber()).intIterator()
                    var outerLoop = false
                    while (intIter.hasNext() && !outerLoop) {   
                      val node = cfg.getNode(intIter.next())
                      println("is " + dst + " dominated by " + node + " " + domInfo.isDominatedBy(dst, node))
                      if (dst != node && domInfo.isDominatedBy(dst, node)) outerLoop = true
                    }
                    println("outerLoop is " + outerLoop)
                    !outerLoop
                  }).contains(dst))}) {
                  //backEdges.getRelated(blk.getNumber()).contains(p.getY())).contains(dst))}) {
              // treat the source of the back edge as a sink for the do loop
              println("got do loop " + p.getY())
              doLoops.add(p.getY())
            }*/
            s + p.getY() 
          } else s
        })
      }
      loopHeaderCache.getOrElseUpdate(ir, { 
        val headers = computeLoopHeaders(ir) 
        //doLoopHeaderCache.put(ir, doLoops.toSet)
        doLoopHeaderCache.put(ir, doLoops)
        headers 
      })
    }
    
    def isLoopHeader(blk : WalaBlock , ir : IR) : Boolean = getLoopHeaders(ir).contains(blk.getNumber())   
    
    /** @return true if blk is a loop header or a loop header falls through to @param blk */
    def findRelatedLoopHeader(blk : WalaBlock, ir : IR) : Option[ISSABasicBlock] = {
      val cfg = ir.getControlFlowGraph()
      val blkNum = blk.getNumber()
      val headers = getLoopHeaders(ir)
         
      
      if (headers.contains(blkNum)) Some(blk)
      else {
        val succs = CFGUtil.getSuccessors(blk, cfg)
        val isCond = CFGUtil.endsWithConditionalInstr(blk)
                
        headers.find(headerNum => {
          val header : WalaBlock = cfg.getNode(headerNum)
          CFGUtil.fallsThroughTo(header, blk, cfg) ||
          // or if one of the headers is a do...while loop header that this block falls through to
          (isDoWhileLoop(header, ir) && succs.contains(header)) || {
            // or if this is a conjunctive loop condition
            val (outOf, into) = getOutOfAndIntoLoopBlocks(header, ir)
            succs.contains(outOf) || succs.contains(into) || into == blk
          }
        }) match {
          case Some(headerNum) => Some(cfg.getNode(headerNum))
          case None => None
        }      
      }
    }
    
    /**
     * get the src of the back edge whose snk is in header
     */
    def getLoopTails(header : WalaBlock , ir : IR) : List[WalaBlock] = {
      require(isLoopHeader(header, ir))
      val headerNum = header.getNumber()
      val cfg =  ir.getControlFlowGraph()
      val backEdges = Acyclic.computeBackEdges(cfg, cfg.entry())
      val srcs = backEdges.collect({case intPair if intPair.getY() == headerNum => new WalaBlock(cfg.getBasicBlock(intPair.getX()))})
      assert(!srcs.isEmpty)
      srcs.toList
    }
    
    def isLoopTail(header : WalaBlock, suspectedTail : WalaBlock, ir : IR) : Boolean = 
      getLoopTails(header, ir).contains(suspectedTail)
            

    /**
     * get all blocks that transition directly to the loop tail that are *not* continue blocks
     */
      /*
    def getLoopTailBlocks(header : WalaBlock, ir : IR) : Set[WalaBlock] = {
      require(isLoopHeader(header, ir))
      val loopTail = getLoopTail(header, ir)
      val cfg = ir.getControlFlowGraph()      
      @annotation.tailrec
      def getLoopTailBlocksRec(blks : Set[WalaBlock], seen : Set[WalaBlock]) : Set[WalaBlock]= {
        // skip blocks ending in a goto -- these are continues and are not part of the loop tail
        val passing = blks.filter (blk => blk == loopTail || CFGUtil.endsWithGotoInstr(blk)) 
        if (passing.isEmpty) seen
        else {
          val toExplore = passing.foldLeft (Set.empty[WalaBlock]) ((set,blk) => {
            val preds = cfg.getNormalPredecessors(blk)
            if (preds.size() < 2) set ++ preds // keep straight-line predecessors only
            else set
          })
          val newSeen = seen.union(passing)
          // explore all succs that we have not already seen
          getLoopTailBlocksRec(toExplore diff newSeen, newSeen)
        }         
      }
      getLoopTailBlocksRec(Set(loopTail), Set.empty)
    }*/
    
    def getLoopTailBlocks(tail : WalaBlock, cfg : SSACFG) : Set[WalaBlock] = 
      CFGUtil.getPredsWhile(tail, cfg, blk => cfg.getNormalPredecessors(blk).size() < 2, true)
        
    // TODO: distinguish between loop header (single basic block that is
    // snk of back edge) and loop conditional block (the block containing the 
    // conditional instruction that controls the loop); there may be blocks in between
    
    def getLoopBody(loopHeader : WalaBlock, ir : IR) : Set[WalaBlock] = {
      require(isLoopHeader(loopHeader, ir))
      val cfg = ir.getControlFlowGraph()
      val tailBlkNum = getPrimaryLoopTail(loopHeader, ir)

      val (outOfLoop, intoLoop) = getOutOfAndIntoLoopBlocks(loopHeader, ir)
      if (DEBUG) println("for BB" + loopHeader.getNumber() + ", intoloop is BB" + intoLoop.getNumber() + " outofloop is BB" + outOfLoop.getNumber())
      val domInfo = getDominators(ir)
      // TODO: do we want the condBlk in the body?
      if (isDoWhileLoop(loopHeader, ir)) {
        // the loop body consists of all blocks that are not dominated by the outOfLoop block and are not the conditional
        //val condBlk = getLoopConditionalBlock(loopHeader, ir).get
        //getSuccsWhile(intoLoop, cfg, (blk => blk != condBlk && !domInfo.isDominatedBy(blk, outOfLoop)))
        if (intoLoop == loopHeader) {
          val succs = cfg.getNormalSuccessors(intoLoop)
          assert (succs.size() == 1, "odd number of successors for intoLoopBlk " + intoLoop + " of explicitly infite do loop " + loopHeader)
          getLoopConditionalBlock(loopHeader, ir) match {
            case Some(condBlk) => 
              val succ = succs.iterator.next()
              //CFGUtil.getSuccsWhile(succ, cfg, (blk => !domInfo.isDominatedBy(blk, outOfLoop)))
              CFGUtil.getSuccsWhile(succ, cfg, (blk => blk != condBlk && !domInfo.isDominatedBy(blk, outOfLoop)))
            case None => sys.error("unexpected: no cond blk for do loop " + loopHeader)
          }          
        } else {          
          assert(intoLoop == outOfLoop) // explicitly infinite loop
          if (DEBUG) println("explicitly infinite do loop; removing do loop from cache")
          // we choose to translate all infinite loops as while loops -- take this out of the loop header cache
          doLoopHeaderCache(ir).remove(loopHeader.getNumber())
          CFGUtil.getSuccsWhile(intoLoop, cfg, (blk => domInfo.isDominatedBy(blk, intoLoop) && (blk.getNumber() <= tailBlkNum || 
             CFGUtil.isThrowBlock(blk, cfg))))
        }
      } else {
        if (DEBUG) println("getting body; tailBlkNum is " + tailBlkNum)
        // can't just check that block number is less than tailBlkNum because sometimes tailBlk is higher in CFG than a throw or return block
        // (see LoopThrowNoRefute test)
        //val body = CFGUtil.getSuccsWhile(intoLoop, cfg, (blk => domInfo.isDominatedBy(blk, intoLoop) && (blk.getNumber() <= tailBlkNum ||
          //CFGUtil.isThrowBlock(blk, cfg))))

        val body = 
          if (intoLoop == outOfLoop) 
            CFGUtil.getSuccsWhile(intoLoop, cfg, (blk => domInfo.isDominatedBy(blk, intoLoop) && 
              (blk.getNumber() <= tailBlkNum || CFGUtil.isThrowBlock(blk, cfg))))
          else 
            CFGUtil.getSuccsWhile(intoLoop, cfg, (blk => domInfo.isDominatedBy(blk, intoLoop) && 
              (blk.getNumber() < outOfLoop.getNumber() || CFGUtil.isThrowBlock(blk, cfg))))
        body ensuring (body => !DEBUG || (tailBlkNum == loopHeader.getNumber() || body.contains(cfg.getBasicBlock(tailBlkNum))), "problem with loop body " + body)
        // the above does not work. the problem is that for disjunctive loop conditions, the block protected by the 
        // disjunction is not dominated by intoLoop...
        // TODO: instead, we rely on block numbers, which is fragile. make this less gross
        //CFGUtil.getSuccsWhile(intoLoop, cfg, blk => (blk.getNumber() <= tailBlkNum) && blk.getNumber() > loopHeader.getNumber()) ensuring
          //(x => x.contains(cfg.getBasicBlock(tailBlkNum)), tailBlkNum + " not in loop body")
      }
    }
    
    
    def isDoWhileLoop(loopHeader : WalaBlock, ir : IR) : Boolean = {
      require(isLoopHeader(loopHeader, ir))
      doLoopHeaderCache.getOrElse(ir, Set.empty[Int]).contains(loopHeader.getNumber())
    }
    
    // return the loop tail that is lowest in the CFG
    def getPrimaryLoopTail(loopHeader : WalaBlock, ir : IR) : Int = {
      val loopTails = getLoopTails(loopHeader, ir)
      // TODO: this is fragile
      val tail = loopTails.maxBy(blk => blk.getNumber()).getNumber()
      if (tail < loopHeader.getNumber()) loopHeader.getNumber() else tail
    }
    
    /**
     * a loop header is a block that is the sink of a back edge, but it may not contain the 
     * conditional instruction that controls whether loop is entered or not. call this block the 
     * "loop conditional block". the loop header should always fall through to the loop conditional
     * block.
     * @return the loop conditional block that loopHeader falls through to
     */
    def getLoopConditionalBlock(loopHeader : WalaBlock, ir : IR) : Option[WalaBlock] = {
      require(isLoopHeader(loopHeader, ir))
      if (CFGUtil.endsWithConditionalInstr(loopHeader)) return Some(loopHeader) 
      val cfg = ir.getControlFlowGraph()
      val loopTails = getLoopTails(loopHeader, ir)
      val tailBlkNum = getPrimaryLoopTail(loopHeader, ir)
      
      var last : WalaBlock = null
      var forLoop = false
      if (isDoWhileLoop(loopHeader, ir)) {
        val preds = cfg.getNormalPredecessors(loopHeader)
        val condPreds = preds.collect({case b if (CFGUtil.endsWithConditionalInstr(b)) => b})
        if (!condPreds.isEmpty) {
          val maxCond = condPreds.maxBy(blk => blk.getNumber())
          // TODO: may not work for breaks or conjunctive loop conds
          if (CFGUtil.getSuccessors(maxCond, cfg).exists(blk => blk.getNumber() >= tailBlkNum)) {
            // get outOfLoopBLk, find earliest pred
            CFGUtil.getSuccessors(cfg.getBasicBlock(tailBlkNum), cfg).find(blk => blk.getNumber() > tailBlkNum) match {
              case Some(outOfLoopBlk) => 
                   val outPreds = CFGUtil.getNormalPredecessors(outOfLoopBlk, cfg).toList
                   //val lowestPred = outPreds.minBy(blk => blk.getNumber())
                   val okPreds = outPreds.filter(pred => pred.getNumber() >= loopHeader.getNumber())
                   assert(!okPreds.isEmpty, s"No predecessors in $outPreds are greater than or equal to $loopHeader: $ir")
                   val lowestPred = okPreds.minBy(blk => blk.getNumber())
                   //assert (lowestPred.getNumber() >= loopHeader.getNumber(), 
                      // s"lowest pred $lowestPred higher than loop header $loopHeader outOfLoopBlk $outOfLoopBlk IR $ir")
                   if (CFGUtil.endsWithConditionalInstr(lowestPred) && 
                       CFGUtil.getSuccsWhile(lowestPred, cfg, blk => blk == lowestPred || (blk != outOfLoopBlk && 
                       outPreds.exists(pred => CFGUtil.fallsThroughTo(blk, pred, cfg))), true).contains(maxCond)) last = lowestPred
                   else last = maxCond
              case None =>
                // there's been some kind of mistake in classifying this as a do while loop. remove it and try again
                if (DEBUG) println("removing " + loopHeader + " from do loop list since we can't find it's outOfLoopBlock")
                doLoopHeaderCache(ir).remove(loopHeader.getNumber())
                return getLoopConditionalBlock(loopHeader, ir) 
            }            
          }
        }
      } else {
        // the loop conditional block is the last block that the loop header falls through to
        CFGUtil.getSuccsWhile(loopHeader, cfg, (blk =>
          if (blk == loopHeader || !isLoopHeader(blk, ir)) cfg.getNormalSuccessors(blk) match {
            case succs if succs.isEmpty() => false
            case succs if succs.size() == 1 => true
            case succs if succs.size() == 2 =>
              // if one of the succs of this is lower in the cfg than the loop tail, it is the loop conditional block. else, it's an explicitly infinite loop
              if (succs.maxBy(blk => blk.getNumber()).getNumber() > tailBlkNum) {
                last = blk
                false
              } else true
              // if the loop is a for (s0; e0; e1) loop, the above check may fail but the e1 part may fall through to the tail block
              //else if (succs.exists(succ => CFGUtil.fallsThroughTo(succ, cfg.getBasicBlock(tailBlkNum), cfg))) {
                //last = blk
                //println("condBlk w/ for loop")
                //forLoop = true
              //x}
              //else last  = null
              //false 
            case succs => true //sys.error("unexpected number of successors for block " + blk + ": " + succs.size())
          } else {
            // if the loop conditional block is itself another loop head, then this is an explicitly infinite loop 
            last = null;
            false 
          }
        )) 
      }
      
      if (DEBUG) println("last is " + last + "tailBlkNum is " + tailBlkNum)
      
      // explicitly infinite loops have no loop conditional block, and in a such a case, we may follow a break and 
      // erroneously find a condBlk outside of the loop), which we detect by checking if last is beyond the loop tail
      if (last == null || (last.getNumber() > tailBlkNum && tailBlkNum != loopHeader.getNumber()) ||
          !CFGUtil.endsWithConditionalInstr(last)) None 
      else {
        //assert(CFGUtil.endsWithConditionalInstr(last), 
          //  s"conditional block $last for loop header $loopHeader should end with conditional. tail block $tailBlkNum IR $ir")
        // TODO: this is fragile. it's possible that last can be a conditional inside of an explicitly
        // infinite loop instead of the loop conditional block. we detect this case by seeing if the 
        // number of the "out of loop block" is less than the number of the loop tail. this relies on the
        // observation that WALA always puts code that occurs after the loop in blocks numbered higher
        // than the loop tail
        //if (cfg.getNormalSuccessors(last).iterator().next().getNumber() < getLoopTail(loopHeader, ir).getNumber()) None
        if (last != loopHeader && tailBlkNum != loopHeader.getNumber() && !forLoop && !isDoWhileLoop(loopHeader, ir) && loopTails.size == 1 && 
            cfg.getNormalSuccessors(last).iterator().next().getNumber() < tailBlkNum) {//loopTails.head.getNumber()) {
          if (DEBUG) println("first succ of " + last + " is higher in CFG than loopTail " + loopTails.head + "; setting to none.")
          None
        }
        else Some(last)
      }
    }
      
    def isExplicitlyInfiniteLoop(loopHeader : WalaBlock, ir : IR) : Boolean = {
      val (into, outOf) = getOutOfAndIntoLoopBlocks(loopHeader, ir)
      into == outOf
    }         
    
    /**
     * @return (outOfLoop, intoLoop) pair, where outOfLoop is the block transitioned to if the loop is not
     * entered, and intoLoop is the block transitioned to if the loop is entered
     */
    def getOutOfAndIntoLoopBlocks(loopHeader : WalaBlock, ir : IR) : (WalaBlock, WalaBlock) = {
      val cfg = ir.getControlFlowGraph()
      getLoopConditionalBlock(loopHeader, ir) match { 
        case Some(condBlk) => 

          if (DEBUG) println("condBlk is " + condBlk)
          val succs = cfg.getNormalSuccessors(condBlk)
          assert(succs.size() == 2)
          val iter = succs.iterator()
          // return (outOfLoop, intoLoop) pair
          val (outOf, into) = { 
            val (out, in) = (iter.next(), iter.next())
            if (isDoWhileLoop(loopHeader, ir)) {
              (in, loopHeader : ISSABasicBlock)
            }
            else 
               if (out.getNumber() > in.getNumber()) (out, in) else (in, out)
          }
          
          
          // if outOf is not greater than the tail block number, then we have a disjunctive loop condition and
          // need to try a bit harder to find the outOf block.
          // TODO: this is fragile and gross 
          val tailBlkNum = getPrimaryLoopTail(loopHeader, ir)      
          if (DEBUG) println("at this point, outOf " + outOf + " and into " + into + " tailBlkNum " + tailBlkNum)

          
          if (outOf.getNumber() < tailBlkNum) {
            var last : WalaBlock = null
            CFGUtil.getSuccsWhile(outOf, cfg, blk => { val found = blk.getNumber() > tailBlkNum; if (found) last = blk; !found})
            assert (last != null)
            (last, into)
          } else (outOf, into)
        case None =>
          if (DEBUG) println("no condBlk; we suspect that " + loopHeader + " is an explicitly infinite loop")                    
          val succs = cfg.getNormalSuccessors(loopHeader)
          assert(succs.size == 1, succs.size() + " succs for suspected infinite loop " + loopHeader + " IR: " + ir)
          val succ = succs.iterator().next()
          (succ, succ) // explicitly infinite loop
      }
    } 
    
    type BlkPair = (WalaBlock,WalaBlock)
    
    /**
     * @return ((breaks, break target) list, (continue, continue target) list) pair
     * This returns *all* breaks and continues in the body of the loop headed by @param loopHeader,
     * not only the ones that break out of the current loop or continue to the head of the current loop.
     * For example, in the program outer : while (...) { inner : while (...) { break outer; } },
     * getBreaksAndContinues([header for inner]) will include "break outer" 
     */
    def getBreaksAndContinues(loopHeader : WalaBlock, ir : IR) : (List[BlkPair], List[BlkPair]) = {
      require(isLoopHeader(loopHeader, ir))
      
      val loopBody = getLoopBody(loopHeader, ir)
      val doLoop = isDoWhileLoop(loopHeader, ir)
      //val condBlk = getLoopConditionalBlock(loopHeader, ir).get.getNumber()
      if (DEBUG) { println("BODY: "); loopBody.foreach(println) }
      val cfg = ir.getControlFlowGraph()
      val loopHeaders = getLoopHeaders(ir)
      val domInfo = getDominators(ir)      
      
      // TODO: two loops can have the same outOfLoop block...
      // map of outOfLoopBlock for loop n -> loopHeader for loop n
      val outOfLoopMap = loopHeaders.foldLeft (Map.empty[WalaBlock,WalaBlock]) ((map, loopHeader) => {
        val loopBlk : WalaBlock = cfg.getNode(loopHeader)
        val (outOfLoopBlk, intoLoopBlk) = getOutOfAndIntoLoopBlocks(loopBlk, ir)
        if (outOfLoopBlk == intoLoopBlk) {
          if (DEBUG) println("triggered special case; looking for outofloop block for " + loopHeader)
          // loopBlk is header for explicitly infinite loop.
          // it may have an out of loop block (if the loop can be broken out of),
          // but it will not transitioned to by the loop head
          //cfg.iterator().toList.minBy(blk => blk.getNumber())
          val bodyBlocks = getLoopBody(loopBlk, ir)
          var last : WalaBlock = null
          //CFGUtil.getSuccsWhile(intoLoopBlk, cfg, blk => { val contains = loopBody.contains(blk); if (!contains) last = blk; blk != loopBlk && contains })
          CFGUtil.getSuccsWhile(intoLoopBlk, cfg, blk => { val contains = loopBody.contains(blk) || blk == loopBlk; if (!contains) last = blk; contains && blk != loopBlk}) 
          if (last == null) map // there is not outOfLoop block; the infinite loop occupies the rest of the procedure
          else map + (last -> loopBlk) // last is an outOfLoop block; add to the map
        } else map + (outOfLoopBlk -> loopBlk)
      })
      
      val (breaks, continues) = 
      loopBody.foldLeft (List.empty[BlkPair], List.empty[BlkPair]) ((lstPair : (List[BlkPair], List[BlkPair]) , blk) => { 
        //if (DEBUG) println("is " + blk + " a break or continue blk?")
        
        def processBreakOrContinue(succ : WalaBlock, 
            lstPair : (List[BlkPair], List[BlkPair])) : (List[BlkPair], List[BlkPair]) = {
          val (breaks, continues) = lstPair
          if (!loopBody.contains(succ)) // breaks and continues jump out of the loop body
            if (domInfo.isDominatedBy(blk, succ)) { //|| fallsThroughToLoopHeadDominating(succ, blk)) {
              // if the block we're jumping to dominates the current block, this is a "while/do loop continue"              
              if (DEBUG) println("adding continue " + blk + " transitions to " + succ)
              (breaks, (blk, succ) :: continues)                
            } else if (!CFGUtil.endsWithReturnInstr(blk)) {
              if (outOfLoopMap.contains(succ)) {
                if (DEBUG) println("adding break " + blk + " transitions to " + succ)
                // this is a break
                // target of break is not the block it is transitioning to, but the *header* of the loop
                // whose outOf block it is transitioning to
                val target = if (isLoopHeader(blk, ir)) {
                  // rare case where a loop header is itself a break
                  // can't use outOfLoopMap here because two loops may have the same out of loop block.
                  loopHeaders.find(blkNum => blkNum != blk.getNumber() && {
                    val loopBlk = cfg.getNode(blkNum)
                    val (outOfLoopBlk, _) = getOutOfAndIntoLoopBlocks(loopBlk, ir)
                    outOfLoopBlk == succ
                  }) match {
                    case Some(headerNum) => new WalaBlock(cfg.getNode(headerNum))
                    case None => sys.error("can't find loop header for outOfLoopBlock " + succ)
                  }
                } else outOfLoopMap.getOrElse(succ, sys.error("can't find loop header for outOfLoopBlock " + succ))        
                ((blk, target) :: breaks, continues)                
              } else {
                val fallThru = CFGUtil.getFallThroughBlocks(succ, cfg);
                //assert(loopHeaders.exists(blkNum => fallThru.contains(cfg.getBasicBlock(blkNum))), 
                    //"can't find loop header that is target of continue " + blk + " -> " + succ)
                // this is a for(s; e0; e1) loop continue; it's continuing to the e1 part 
                // or, it's a do loop continue
                if (DEBUG) println("adding for/do loop continue " + blk + " transitions to " + succ)
                (breaks, (blk, succ) :: continues)                
              }
            } else lstPair //else if (loopTailBlocks.contains(succ) && !loopTailBlocks.contains(blk)) {
          else lstPair
        }
        
        val succs = cfg.getNormalSuccessors(blk)
        succs.foldLeft (lstPair) ((lstPair, succ) => processBreakOrContinue(succ, lstPair))
        //if (succs.size() == 1) succs.foldLeft (lstPair) ((lstPair, succ) => processBreakOrContinue(succ, lstPair))
        //else lstPair
        /*
        succs.size() match {
          case 1 => 
            val succ = succs.iterator().next()
            if (!loopBody.contains(succ)) // breaks and continues jump out of the loop body
              if (domInfo.isDominatedBy(blk, succ)) { //|| fallsThroughToLoopHeadDominating(succ, blk)) {
                // if the block we're jumping to dominates the current block, this is a "while/do loop continue"              
                if (DEBUG) println("adding continue " + blk + " transitions to " + succ)
                (breaks, (blk, succ) :: continues)                
              } else if (!CFGUtil.endsWithReturnInstr(blk)) {
                if (loopHeaders.contains(succ.getNumber())) println("loop headers have " + succ)
                if (outOfLoopMap.contains(succ)) {
                  if (DEBUG) println("adding break " + blk + " transitions to " + succ)
                  // this is a break
                  // target of break is not the block it is transitioning to, but the *header* of the loop
                  // whose outOf block it is transitioning to
                  val target = outOfLoopMap.getOrElse(succ, sys.error("can't find loop header for outOfLoopBlock " + succ))
                  ((blk, target) :: breaks, continues)
                } else {
                  val fallThru = CFGUtil.getFallThroughBlocks(succ, cfg);
                  assert(loopHeaders.find(blkNum => fallThru.contains(cfg.getBasicBlock(blkNum))).isDefined, 
                         "can't find loop header that is target of continue " + succ)
                  // this is a for(s; e0; e1) loop continue; it's continuing to the e1 part 
                   if (DEBUG) println("adding for loop continue " + blk + " transitions to " + succ)
                  (breaks, (blk, succ) :: continues)                
                }
              } else lstPair //else if (loopTailBlocks.contains(succ) && !loopTailBlocks.contains(blk)) {
              // if the block we're jumping to is inside the loop and it falls through to a 
              // loop head dominating the current block, this is a "for loop continue"
              //if (DEBUG) println("adding for loop continue " + blk + " transitions to " + succ)
              //(breaks, (blk, succ) :: continues)                
            else lstPair
          case _ => lstPair
        } 
        */
      })
      (breaks, continues)
    }
    
    def getBreaks(loopHeader : WalaBlock, ir : IR) : List[BlkPair] = getBreaksAndContinues(loopHeader, ir)._1    
    def getContinues(loopHeader : WalaBlock, ir : IR) : List[BlkPair] = getBreaksAndContinues(loopHeader, ir)._2
    // get the sources of all break and continue pairs for this loop header 
    def getBreakAndContinueSources(loopHeader : WalaBlock, ir : IR): Set[WalaBlock] = {
      val (walaBreaks, walaContinues) = getBreaksAndContinues(loopHeader, ir)
      walaBreaks.foldLeft (walaContinues.unzip._1) ((lst, pair) => pair._1 :: lst).toSet
    }
    def getBreakAndContinueMap(loopHeader : WalaBlock, ir : IR): Map[WalaBlock,WalaBlock] = {
      val (walaBreaks, walaContinues) = getBreaksAndContinues(loopHeader, ir)
      walaContinues.foldLeft (walaBreaks.foldLeft (Map.empty[WalaBlock,WalaBlock]) ((map, pair) => map + pair)) ((map, pair) => {
        //assert (!map.contains(pair._1), pair._1 + " is both a break and a continue!")
        map + pair
      })
    }
    
    def getContinueTarget(continueBlk : WalaBlock, cfg : SSACFG) = {
      val succs = cfg.getNormalSuccessors(continueBlk)
      assert (succs.size() == 1)
      succs.iterator().next()
    }
        
  }
     