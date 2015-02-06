package edu.colorado.hopper.client.bounds

import com.ibm.wala.ipa.cfg.ExceptionPrunedCFG
import com.ibm.wala.ssa.{ISSABasicBlock, SSAPhiInstruction}
import edu.colorado.hopper.client.bounds.ArrayBoundsSymbolicExecutor._
import edu.colorado.hopper.executor.{TransferFunctions, UnstructuredSymbolicExecutor}
import edu.colorado.hopper.jumping.{JumpingSymbolicExecutor, RelevanceRelation}
import edu.colorado.hopper.state.Path
import edu.colorado.thresher.core.Options
import edu.colorado.walautil.{CFGUtil, LoopUtil}

import scala.collection.JavaConversions._

object ArrayBoundsSymbolicExecutor {
  private val DEBUG = Options.SCALA_DEBUG
  private val TRACE = false
}

class JumpingArrayBoundsSymbolicExecutor(override val tf : TransferFunctions,
                                         override val rr : RelevanceRelation,
                                         override val keepLoopConstraints : Boolean = true)
  extends JumpingSymbolicExecutor with ArrayBoundsSymbolicExecutor

class DefaultArrayBoundsSymbolicExecutor(override val tf : TransferFunctions,
                                         override val keepLoopConstraints : Boolean = true) extends ArrayBoundsSymbolicExecutor
  
/** New symbolic executor that doesn't always drop pure constraints. instead, it uses Z3 to help infer loop invariants */
trait ArrayBoundsSymbolicExecutor extends UnstructuredSymbolicExecutor {

  override def executeBackwardIntraproceduralWhile(p : Path, passPaths : List[Path], failPaths : List[Path], test : Path => Boolean) : (List[Path], List[Path]) = {
    if (TRACE) logMethodAndTime("executeBackwardIntraproceduralWhile")
    val startBlk = p.blk
    val ir = p.node.getIR()    
    
    // loop header--see if the invariant says we can stop executing
    def invariantImpliesPath(p : Path) : Boolean = {
      val res = loopInvMap.pathEntailsInv(p.callStack.stack.map(f => (f.node, f.blk)), p)
      if (DEBUG && res) println("Hit fixed point at loop head  " + startBlk)
      res
    }
    
    val loopHeader = LoopUtil.findRelatedLoopHeader(startBlk, ir)
    loopHeader.foreach(loopHeader => 
      if (CFGUtil.endsWithConditionalInstr(startBlk)) {
        if (DEBUG) println("at loop head BB" + loopHeader.getNumber() + " on path " + p)
        val thenBranch = CFGUtil.getThenBranch(startBlk, p.node.getIR().getControlFlowGraph())
        // don't do the loop invariant check if we're coming from outside the loop!
        if ((p.lastBlk != thenBranch || LoopUtil.isDoWhileLoop(loopHeader, ir)) && 
            invariantImpliesPath(p)) return (passPaths, failPaths)
      } else if (LoopUtil.isExplicitlyInfiniteLoop(loopHeader, ir) && // won't have any conditional branch instruction in this case
                 invariantImpliesPath(p)) return (passPaths, failPaths)     
    )
    
    val instrPaths = executeBlkInstrs(p, true)
    if (instrPaths.isEmpty) (passPaths, failPaths)
    else {
      // if single predecessor, go to pred
      // if multiple predecessors, identify join point and execute each side until join point is reached      
      val cfg = ir.getControlFlowGraph()      
      val preds = cfg.getNormalPredecessors(startBlk)
      if (DEBUG) println("done with " + startBlk + ", getting preds")
      // TODO: do we have to drop here? can we drop only when we follow a back edge instead      

      preds.size() match {
        case 0 =>
          if (DEBUG) println("0 preds, doing return")
          if (!cfg.getExceptionalPredecessors(startBlk).isEmpty()) {
            // have no normal predecessors, but do have exceptional ones. refute
            // based on thrown exception
            if (Options.PRINT_REFS) println("refuted by thrown exception!")
            (passPaths, failPaths)
          } else {
            // TODO: returnToCaller filters by test, but after setting new block. 
            // we do it here to handle the case where we want to return before setting a new block
            // TODO: this is more than a bit weird--we should do something for the case where newPassPaths
            // is a non-empty subset of instrPaths
            val (newPassPaths, newFailPaths) = filterFailPaths(instrPaths, passPaths, failPaths, test)
            if (newPassPaths.isEmpty) (newPassPaths, newFailPaths)
            else returnToCaller(instrPaths, passPaths, failPaths, test)
          }
        case 1 => 
          assert (!instrPaths.head.blk.iteratePhis().hasNext(), "block " + instrPaths.head.blk + " has unexpected phis! " + p.node.getIR)
          val pred = preds.iterator().next()
          if (DEBUG) println("single pred BB" + pred.getNumber())
          instrPaths.foreach(p => p.setBlk(pred))
          filterFailPaths(instrPaths, passPaths, failPaths, test)          
        case n => 
          if (DEBUG) { print(" > 1 pred "); preds.foreach(p => print(" BB" + p.getNumber())); println }
          val p = instrPaths.head
          val blk = p.blk
          val phis = p.blk.iteratePhis().toIterable
              
          // push all paths up to the join
          val initCallStackSize = p.callStackSize
          val prunedCFG = ExceptionPrunedCFG.make(cfg)
          val predList = preds.toList.filter(blk => prunedCFG.containsNode(blk))            
          // this is a weird case that arises with explicitly infinite loops or ony exceptional predecessors
          // refute, since there's no way we ever could have gotten here
          if (predList.isEmpty || prunedCFG.getNumberOfNodes() == 0) (passPaths, failPaths)
          else {
            val domInfo = getDominators(prunedCFG)          
            val forkMap = getForkMap(blk, predList, instrPaths, phis,
                domInfo, ir, loopHeader)    
            if (!forkMap.isEmpty) {
              val paths = executeToJoin(blk, predList.reverse, forkMap, domInfo, initCallStackSize, cfg)
              filterFailPaths(paths, passPaths, failPaths, test)
            } else (passPaths, failPaths)
          }
       }
    }
  }  
  
  override def getForkMapInternal(preds : Iterable[ISSABasicBlock], instrPaths : List[Path], 
      phis : Iterable[SSAPhiInstruction], 
      loopHeader : Option[ISSABasicBlock],
      extraCheck : (ISSABasicBlock, Path) => Boolean = (_ ,_) => true) : Map[ISSABasicBlock,List[Path]] = {
      if (TRACE) logMethodAndTime("getForkMapInternal")
    (preds.view.zipWithIndex foldLeft Map.empty[ISSABasicBlock,List[Path]]) { case (forkPathMap, (pred, phiIndex)) => 
      instrPaths.foldLeft (forkPathMap) ((forkPathMap, p) => {
        val paths = forkPathMap.getOrElse(pred, List.empty[Path])
        forkPathMap + (pred -> {
          val newP = p.deepCopy
          if (phis.forall(phi => newP.executePhi(phi, phiIndex, tf)) && extraCheck(pred, newP)) {
            newP.setBlk(pred)
            loopHeader match {
              // drop constraints if we traverse a back edge
              case Some(loopHeader) if (LoopUtil.isLoopTail(loopHeader, pred, newP.node.getIR())) =>
                newP.dropLoopProduceableConstraints(loopHeader, tf)                
              case _ => ()                
            }
            newP :: paths
          } else paths // refuted by executing phi
        })
      })
    }
  }
    
}