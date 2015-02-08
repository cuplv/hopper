package edu.colorado.hopper.executor

import com.ibm.wala.analysis.typeInference.TypeInference
import com.ibm.wala.cfg.ControlFlowGraph
import com.ibm.wala.classLoader.IClass
import com.ibm.wala.ipa.callgraph.{CGNode, CallGraph}
import com.ibm.wala.ipa.cfg.ExceptionPrunedCFG
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.shrikeBT.IConditionalBranchInstruction.Operator.EQ
import com.ibm.wala.ssa._
import com.ibm.wala.types.{MethodReference, TypeReference}
import com.ibm.wala.util.graph.dominators.Dominators
import com.twitter.util.LruMap
import edu.colorado.hopper.executor.UnstructuredSymbolicExecutor._
import edu.colorado.hopper.state._
import edu.colorado.thresher.core.Options
import edu.colorado.walautil._
import edu.colorado.walautil.Types.WalaBlock

import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator, asScalaSet, collectionAsScalaIterable, mapAsJavaMap}

object UnstructuredSymbolicExecutor {
  protected[executor] def DEBUG = Options.SCALA_DEBUG
  protected[executor] def MIN_DEBUG = DEBUG
  private[executor] val TRACE = false
  private[executor] val PRINT_IR = false
  // save invariant maps that lead to refutations
  private val SAVE_INVARIANT_MAPS = false

  // add path constraints from switch upon entering block rather than upon crossing case expression
  private val PRE_CONSTRAIN_SWITCHES = true

  private val timekeeper = new Timer
}

class DefaultSymbolicExecutor(override val tf : TransferFunctions,
                              override val keepLoopConstraints : Boolean = false) extends UnstructuredSymbolicExecutor {}

trait UnstructuredSymbolicExecutor extends SymbolicExecutor {
  val tf : TransferFunctions

  // if true, keep path constraints from loop heads. otherwise, drop them
  val keepLoopConstraints : Boolean
  
  object WitnessFoundException extends Exception 
  object BudgetExceededException extends Exception
  
  def cg : CallGraph = tf.cg
  def cha : IClassHierarchy = tf.cha
  
  val domCache = new LruMap[ControlFlowGraph[SSAInstruction,ISSABasicBlock],Dominators[ISSABasicBlock]](25)
  def getDominators(cfg : ControlFlowGraph[SSAInstruction,ISSABasicBlock]) : Dominators[ISSABasicBlock] =
    domCache.getOrElseUpdate(cfg, Dominators.make(cfg, cfg.entry))
  
  def cleanup() : Unit = {
    clearInvariantMaps
    domCache.clear
    edu.colorado.thresher.core.WALACFGUtil.clearCaches()
  }
    
  protected def filterFailPaths(toProcess : Iterable[Path], passPaths : List[Path], failPaths : List[Path], test : Path => Boolean) : (List[Path], List[Path]) =     
    toProcess.foldLeft (passPaths, failPaths) ((pair, path) => { 
      val (passPaths, failPaths) = pair
      if (test(path)) (path :: passPaths, failPaths)
      else (passPaths, path :: failPaths)
    })
  
  def handleFakeWorldClinit(p : Path, failPaths : List[Path] = List.empty[Path]) : List[Path] = {
    val fakeWorldClinit = CGNodeUtil.getFakeWorldClinitNode(cg).get
    if (p.foundWitness) List(p)
    else if (!cg.containsNode(fakeWorldClinit)) Nil
    else {   
      val lastNode = p.popCallStack      
      assert(lastNode.node == fakeWorldClinit, "expected fakeWorldClinit, got " + lastNode)
      assert(p.callStack.isEmpty)
      p.setNode(fakeWorldClinit) // sets current node, blk, and line # to the end of fakeWorldClinit
      assert(p.callStack.size == 1)
      val clinitEntry = p.node.getIR().getControlFlowGraph().entry()
      val paths = executeBackwardUntilWitnessFound(List(p), path => path.blk != clinitEntry || path.index > -1, failPaths)
      if (paths.isEmpty) failPaths
      //else if (paths.size == 1 && paths(0) == p)
      // compare heap.pure constraints instead of call stacks because there are block/index matching issues
      // that cause us to fail to recognize when two paths are (in fact) equal
      else if (paths.size == 1 && paths(0).qry.heapConstraints == p.qry.heapConstraints &&
                                  paths(0).qry.pureConstraints == p.qry.pureConstraints) 
        //if (p.initializeStaticFieldsToDefaultValues) p :: failPaths else failPaths
        if (p.initializeStaticFieldsToDefaultValues) {
          if (p.foundWitness) throw WitnessFoundException
          else failPaths // this case happens when we have a constraint that was never consumed
        } else failPaths // refuted by initialization to default values
      else {
        assert(p.callStack.size == 1)
        paths.foreach(p => assert(p.callStack.size == 1))
        paths.foldLeft (failPaths) ((failPaths, p) => handleFakeWorldClinit(p))
      } 
    }
  }
  
  // special case of executeBackwardUntil thats stops upon finding a witness, throws exception to return to top level
  def executeBackwardUntilWitnessFound(passPaths : List[Path], test : Path => Boolean = Util.RET_TRUE, 
      failPaths : List[Path] = List.empty[Path]) : List[Path] = 
    executeBackwardWhile(passPaths, (p => if (p.foundWitness) throw WitnessFoundException else test(p)), failPaths)

  def handleEmptyCallees(paths : List[Path], i : SSAInvokeInstruction, caller : CGNode) : List[Path] = {
    if (DEBUG) println("Dropping retval constraint because we have no targets")
    // callee is a native method or cannot be resolved for some reason. drop any retval constraints we have
    paths.foreach(p => p.dropReturnValueConstraints(i, caller, tf))
    paths
  }

  // return (list of paths that entered callee, list of paths that have chosen to skip callee)
  def enterCallee(paths : List[Path], i : SSAInvokeInstruction) : (List[Path], List[Path]) = {
    if (TRACE) logMethodAndTime("enterCallee")
    val caller = paths.head.node
    tf.handleJavaMagicMethod(i, caller, paths) match {
      case Some(res) => res
      case None =>
        val callees = cg.getPossibleTargets(caller, i.getCallSite())
        if (callees.isEmpty()) {
          // check for null dispatch
          val okPaths = paths.filter(p => tf.isDispatchFeasible(i, caller, p.qry))
          val retPaths = handleEmptyCallees(okPaths, i, caller)
          (List.empty[Path], retPaths)
        } else paths.foldLeft (List.empty[Path], List.empty[Path]) ((pair, p) =>
          callees.foldLeft (pair) ((pair, callee) => {
            val calleePath = p.deepCopy
            if (PRINT_IR) println(callee.getIR())
            val (enterPaths, skipPaths) = pair

            val qry = calleePath.qry
            if (tf.isDispatchFeasible(i, caller, qry) && tf.isRetvalFeasible(i, caller, callee, qry) &&
                callee.getMethod().getReference() != Path.SYSTEM_EXIT) {
              if (Path.methodBlacklistContains(callee.getMethod())) {
                // skip method if it is in our blacklist
                calleePath.dropReturnValueConstraints(i, caller, tf)
                (enterPaths, if (skipPaths.contains(calleePath)) skipPaths else calleePath :: skipPaths)
              } else if (calleePath.callStackSize >= Options.MAX_CALLSTACK_DEPTH || callee.getIR == null ||
                callee == caller) {
                if (DEBUG)
                  println("skipping call to " + callee.getMethod.getName() + " due to " +
                    (if (calleePath.callStackSize >= Options.MAX_CALLSTACK_DEPTH) "depth-out"
                    else if (callee.getIR == null) "null IR"
                    else if (callee == caller) "recursion"
                    else "blacklist")
                  )
                tf.dropConstraintsFromInstructions(List(i), caller, qry, Some(callee))
                (enterPaths, if (skipPaths.contains(calleePath)) skipPaths else calleePath :: skipPaths)
              } else if (calleePath.isCallRelevant(i, caller, callee, tf))
                // calling enterCallee pushes callee onto call stack
                (if (tf.enterCallee(i, calleePath.qry, calleePath.node, callee)) calleePath :: enterPaths else enterPaths,
                  skipPaths)
              else {
                if (DEBUG) println("callee not relevant; skipping. skip paths have " + skipPaths.size)
                (enterPaths, if (skipPaths.contains(calleePath)) skipPaths else calleePath :: skipPaths)
              } // callee feasible, but not relevant; skip it
            } else {
              if (DEBUG) println("Refuted by bad dispatch, bad retval, or call to System.exit()!")
              (enterPaths, skipPaths)
            }
          })
        )
    }
  }

  def executeInstr(paths : List[Path], instr : SSAInstruction, blk : ISSABasicBlock, node : CGNode, cfg : SSACFG,
                   isLoopBlk : Boolean, callStackSize : Int) : List[Path] = instr match {
    case instr : SSAInvokeInstruction =>
      val (enterPaths, skipPaths) = enterCallee(paths, instr)
      if (!enterPaths.isEmpty) {
        if (MIN_DEBUG)
          println(s"Entering call ${ClassUtil.pretty(instr.getDeclaredTarget())} from ${ClassUtil.pretty(node)}; ${enterPaths.size} targets.")
        if (DEBUG)
          println(s"Entering call ${instr.getDeclaredTarget().getName()} from ${node.getMethod().getName()} full names ${ClassUtil.pretty(instr.getDeclaredTarget())} from ${ClassUtil.pretty(node)}")
        val paths = executeBackwardWhile(enterPaths, p => p.callStackSize != callStackSize, skipPaths)
        if (DEBUG)
          println(s"Returning from call to ${ClassUtil.pretty(instr.getDeclaredTarget())} back to ${ClassUtil.pretty(node)}; have ${paths.size} paths.")
        paths
      } else {
        if (DEBUG)
          if (!skipPaths.isEmpty) println(s"decided to skip call $instr; have ${skipPaths.size}")
          else println(s"Refuted by call to $instr")
        skipPaths
      }
    case instr : SSAPhiInstruction => paths // skip phis here, we deal with them while branching to preds //sys.error("phi " + instr)
    case instr : SSAConditionalBranchInstruction =>
      if (!isLoopBlk || keepLoopConstraints)
        paths.foldLeft (List.empty[Path]) ((paths, p) =>
          // might add a constraint that we would prefer not to pick up here, but we can hopefully eliminate it at the join point
          if (p.addConstraintFromConditional(instr, isThenBranch = (p.lastBlk == CFGUtil.getThenBranch(blk, cfg)), tf)) p :: paths
          else paths
        )
      else paths
    case instr : SSASwitchInstruction => handleSwitch(paths, instr, blk, cfg)
    case instr =>
      paths.foldLeft (List.empty[Path]) ((paths, p) => p.executeInstr(instr, tf) match {
        case None => paths
        case Some(newPaths) => newPaths ++ paths
      })
  }
  
  def executeBlkInstrs(p : Path, isLoopBlk : Boolean) : List[Path] = {
    if (TRACE) logMethodAndTime("executeBlkInstrs")
    // TODO: all paths should have the same index here -- should do quick check for -1 index
    val pathIndex = p.index
    if (pathIndex < 0) List(p) // no need to execute any instrs for invalid indices 
    else {
      val node = p.node
      val ir = node.getIR
      val cfg = ir.getControlFlowGraph()
      val blk = p.blk
      val instrs = blk.asInstanceOf[SSACFG#BasicBlock].getAllInstructions()

      (instrs.view.zipWithIndex.reverse foldLeft List(p)) { case (paths : List[Path], (instr : SSAInstruction, index : Int)) =>
        if (index <= pathIndex) {
          if (MIN_DEBUG) { print("INSTR : "); ClassUtil.pp_instr(instr, node.getIR()); println }          
          if (DEBUG && paths.size > 1) println("Have " + paths.size + " paths")
          paths.foreach(p => p.setIndex(index - 1)) // update index on every path
          if (Options.SOUND_EXCEPTIONS && instr.isPEI) {
            // return (pathsNotToExecute, pathsToExecute) pair
            def partitionExceptionalAndNormalPaths(thrownExceptionTypes : Iterable[IClass]) : (List[Path],List[Path]) = {
              // split paths into exceptional and non-exceptional ones. don't execute the exceptional ones. if the
              // instruction can throw an exception that explains the exceptional path, mark the path as non-exceptional
              // so that the previous instruction will be executed. this is safe to do because WALA places at most one PEI
              // instruction in each block, and the CFG has an exceptional edge to every block containing a PEI
              paths.partition(p => {
                if (p.couldCatchThrownExceptionType(thrownExceptionTypes, cha)) p.clearExceptionTypes()
                p.isExceptional
              })
            }

            val thrownExceptionTypes = instr.getExceptionTypes.map(typ => cha.lookupClass(typ))
            instr match {
              case i : SSAThrowInstruction => // throw e
                // throw is a special case since the WALA docs say getExceptionTypes doesn't work for throw
                val typeInference = TypeInference.make(ir, true)
                val excTypeRef = typeInference.getType(i.getException).getTypeReference
                val feasiblePaths =
                  if (excTypeRef == null) {
                    // null signifies type inference failure; top was inferred. any exception could be thrown. keep
                    // the exceptional paths and mark them as non-exceptional, refute all other paths
                    paths.filter(p => p.isExceptional)
                  } else {
                    val thrownExceptionTypes = List(cha.lookupClass(excTypeRef))
                    // keep exceptional paths that could have caught e, refute other paths
                    paths.filter(p => p.isExceptional && p.couldCatchThrownExceptionType(thrownExceptionTypes, cha))
                }
                feasiblePaths.foreach(p => p.clearExceptionTypes())
                feasiblePaths
              case i : SSAInvokeInstruction =>
                // calls are a special case. we have to execute even pathsNotToExecute to account for the possibility
                // that an exception was thrown inside of the call
                val (pathsNotToExecute, _) = partitionExceptionalAndNormalPaths(thrownExceptionTypes)
                val pathsNotToExecuteCopy = pathsNotToExecute.map(p => p.deepCopy)
                executeInstr(paths, instr, blk, node, cfg, isLoopBlk, p.callStackSize).union(pathsNotToExecuteCopy)
              case _ =>
                val (pathsNotToExecute, _) = partitionExceptionalAndNormalPaths(thrownExceptionTypes)
                // keep exceptional paths that could have caught e, refute other paths
                val feasibleExceptionalPaths = pathsNotToExecute.filter(p => !p.isExceptional)
                executeInstr(paths, instr, blk, node, cfg, isLoopBlk, p.callStackSize).union(feasibleExceptionalPaths)
            }
          } else executeInstr(paths, instr, blk, node, cfg, isLoopBlk, p.callStackSize)
        } else paths
      }
    }
  }
  
  def getCallers(cg : CallGraph, callee : CGNode) : Iterable[CGNode] = cg.getPredNodes(callee).toIterable
  
  def returnFromCall(p : Path) : Iterable[Path] = {
    val callee = p.callStack.top.node // get rid of current stack frame

    if (p.callStackSize == 1) {
      // no calling context; have to consider all callers in call graph
      if (DEBUG) println("at function boundary of node " + ClassUtil.pretty(callee))      
      
      if (callee == CGNodeUtil.getFakeWorldClinitNode(cg).get) sys.error("should be handled elsewhere")
      // TODO: execute other entrypoints also? answer depends on harness
      else if (callee == cg.getFakeRootNode() || callee.getMethod().isClinit()) List(p)
      else { // else, return to caller with no context
        val callers = getCallers(cg, callee)
        if (MIN_DEBUG) println(s"Context-free return; branching from ${ClassUtil.pretty(callee)} to ${callers.size} callers.")
        val newPaths = callers.foldLeft (List.empty[Path]) ((lst, caller) => {
          val callerPath = p.deepCopy
          // create a path for each caller and call site of the current method
          if (MIN_DEBUG) println("caller: " + ClassUtil.pretty(caller))
          if (callerInvMap.pathEntailsInv((caller, callee), callerPath)) {
            if (Options.PRINT_REFS) println("Refuted by caller summary.")
            lst // refuted by summary
          } else {
            if (UnstructuredSymbolicExecutor.PRINT_IR) println(caller.getIR())
            val recursive = caller.equals(callee)
            val callerIR = caller.getIR()
            val callerCFG = callerIR.getControlFlowGraph()

            // get all call instructions in caller that might call callee
            callerIR.getInstructions().zipWithIndex.collect({
              case (i : SSAInvokeInstruction, index) if cg.getPossibleTargets(caller, i.getCallSite()).contains(callee) => (i, index)
            })
            .foldLeft (lst) ((lst, pair) => {
              val (invoke, index) = pair
              val sitePath = callerPath.deepCopy
              if (recursive) {
                // TODO: handle mutual recursion here? need to track repeated sequences of bw visited calls
                if (DEBUG) println("handled recursive call while forking to all callers--dropping constraints")
                sitePath.dropConstraintsProduceableInCall(invoke, caller, callee, tf)
              }
              val callBlk = callerCFG.getBlockForInstruction(index)
              // call is always the last instruction in a block. set to line *before* the call
              val callLine = callBlk.asInstanceOf[SSACFG#BasicBlock].getAllInstructions().size - 2          
              assert(callBlk.getLastInstruction == invoke,
                     s"Expected call to be last instruction in $callBlk, but got ${callBlk.getLastInstruction}. IR $callerIR")
              if (sitePath.returnFromCall(caller, callee, callBlk, callLine, invoke, tf)) {
                assert(sitePath.node == caller)
                sitePath :: lst
              } else {
                if (Options.PRINT_REFS) println("refuted by return from call")
                lst
              }
            })
          }
        })
        newPaths
      }
    } else // else callStack.size > 1, "normal" return from callee to caller      
      p.callStack.top.callInstr match {
        case Some(callInstr) => 
          if (!p.returnFromCall(callInstr, callee, tf)) Nil
          else List(p)
        case None => sys.error("Expecting call instruction, but found nothing: " + p.callStack)
      }
  } ensuring (_.forall(newP => !(newP.callStackSize == 0)))
  
  def returnToCaller(paths : List[Path], passPaths : List[Path], failPaths : List[Path], 
                     test : Path => Boolean = Util.RET_TRUE) : (List[Path], List[Path]) =
    paths.foldLeft (passPaths, failPaths) ((pathPair, path) => {
      val (passPaths, failPaths) = pathPair
      val callee = path.node
      val fakeClinit = CGNodeUtil.getFakeWorldClinitNode(cg).get
      if (callee.equals(fakeClinit) || 
          callee.getMethod().isClinit() || path.node.equals(cg.getFakeRootNode())) {
        // special case for fakeWorldClinit
        paths.foreach(p => if (p.foundWitness) throw WitnessFoundException)
        if (callee.getMethod.isClinit()) {
          assert(path.initializeStaticFieldsToDefaultValues)
        }
        if (DEBUG) println("starting fakeWorldClinit handling")
        path.popCallStack
        if (test(path)) {
          assert(path.callStack.isEmpty, "Expected empty call stack but got " + path.callStack)
          path.setNode(fakeClinit)
          
          val clinitPaths = handleFakeWorldClinit(path, failPaths)
          if (DEBUG) println("done with fakeWorldClinit handling returning " + clinitPaths.size)
          (passPaths, clinitPaths)
        } else (passPaths, path :: failPaths)
      } else {
        // normal case: reached function boundary; perform return from function
        filterFailPaths(returnFromCall(path), passPaths, failPaths, test)
      }
    })
    
    
  def getInvariantMaps : List[InvariantMap[_ <: Any]] = List(callerInvMap, loopInvMap)
  def cloneInvariantMaps : List[InvariantMap[_ <: Any]] = getInvariantMaps.map(invMap => invMap.clone)
  // replace the current invariant maps with the ones in newMaps
  def resetInvariantMaps(newMaps : List[InvariantMap[_ <: Any]]) : Unit = {
    this.callerInvMap = newMaps(0).asInstanceOf[InvariantMap[(CGNode,CGNode)]] 
    this.loopInvMap = newMaps(1).asInstanceOf[InvariantMap[Iterable[(CGNode,ISSABasicBlock)]]]     
  }
  
  def clearInvariantMaps() : Unit = {
    callerInvMap.clear
    loopInvMap.clear
  }
  
  var callerInvMap = new InvariantMap[(CGNode,CGNode)]
  var loopInvMap = new InvariantMap[Iterable[(CGNode,ISSABasicBlock)]]
  
  def executeBackwardIntraproceduralWhile(p : Path, passPaths : List[Path], failPaths : List[Path], test : Path => Boolean) : (List[Path], List[Path]) = {
    if (TRACE) logMethodAndTime("executeBackwardIntraproceduralWhile")
    val startBlk = p.blk
    val ir = p.node.getIR()

    // loop header--see if the invariant says we can stop executing
    def invariantImpliesPath(p: Path): Boolean = {
      val res = loopInvMap.pathEntailsInv(p.callStack.stack.map(f => (f.node, f.blk)), p)
      if (DEBUG && res) println(s"Hit fixed point at loop head $startBlk")
      res
    }

    val loopHeader = LoopUtil.findRelatedLoopHeader(startBlk, ir)
    loopHeader.foreach(loopHeader =>
      if (CFGUtil.endsWithConditionalInstr(startBlk)) {
        if (DEBUG) println(s"at loop head BB${loopHeader.getNumber()} on path $p")
        // don't do the loop invariant check if we're coming from outside the loop
        if ((LoopUtil.getLoopBody(loopHeader, ir).contains(p.lastBlk) || LoopUtil.isDoWhileLoop(loopHeader, ir)) &&
            invariantImpliesPath(p))
          return (passPaths, failPaths)
      } else if (LoopUtil.isExplicitlyInfiniteLoop(loopHeader, ir) && // won't have any conditional branch instruction in this case
                 invariantImpliesPath(p))
        return (passPaths, failPaths)
    )

    val isLoopBlk = loopHeader.isDefined/*loopHeader match {
      case Some(loopHeader) => loopHeader == p.blk
      case None => false
    }*/

    val instrPaths = executeBlkInstrs(p, isLoopBlk)
    if (instrPaths.isEmpty) (passPaths, failPaths)
    else forkToPredecessorBlocks(instrPaths, startBlk, loopHeader, ir, passPaths, failPaths, test)
  }

  def forkToPredecessorBlocks(instrPaths : List[Path], startBlk : ISSABasicBlock, loopHeader : Option[ISSABasicBlock],
                              ir : IR, passPaths : List[Path], failPaths : List[Path], test : Path => Boolean) = {
    // if single predecessor, go to pred
    // if multiple predecessors, identify join point and execute each side until join point is reached
    val cfg = ir.getControlFlowGraph()

    if (Options.SOUND_EXCEPTIONS && startBlk.isCatchBlock) {
      // if we are going backward from a catch block, mark all paths as exceptional
      val caughtExceptionTypes = startBlk.getCaughtExceptionTypes.toSet
      if (DEBUG) println(s"setting paths to exceptional; types are $caughtExceptionTypes")
      instrPaths.foreach(p => p.setExceptionTypes(caughtExceptionTypes, cha))
      if (DEBUG && !caughtExceptionTypes.isEmpty) instrPaths.foreach(p => assert(p.isExceptional))
    }

    val preds =
      if (Options.SOUND_EXCEPTIONS && instrPaths.exists(p => p.isExceptional)) cfg.getPredNodes(startBlk).toList
      else cfg.getNormalPredecessors(startBlk).toList
    if (DEBUG) println("done with " + startBlk + ", getting preds")
      
      // dropping constraints here ensures that we never carry on the loop condition. this is desirable for many clients
      // that do not require precise reasoning about loop conditions, since we will never waste effort trying to refute
      // based on constraints involving the loop condition. on the other hand, this is NOT desirable for clients that do
      // require precise reasoning about the loop condition. this is why clients such as array bounds implement a
      // variation on this symbolic executor that chooses to do something different here
      loopHeader.foreach(loopHeader => {
        if (DEBUG) println("Found related loop head BB" + loopHeader.getNumber() + "; dropping constraints")
        instrPaths.foreach(p => p.dropLoopProduceableConstraints(loopHeader, tf))
      })

    preds.size match {
      case 0 =>
        if (DEBUG) println("0 preds, doing return")
        if (!cfg.getExceptionalPredecessors(startBlk).isEmpty()) {
          // have no normal predecessors, but do have exceptional ones. refute based on thrown exception. note that
          // this branch will never be entered in SOUND_EXCEPTIONS mode
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
        assert (!instrPaths.head.blk.iteratePhis().hasNext(), s"block ${instrPaths.head.blk} has unexpected phis! $ir")
        val pred = preds.head
        if (DEBUG) println(s"single pred BB${pred.getNumber()}")
        instrPaths.foreach(p => p.setBlk(pred))
        filterFailPaths(instrPaths, passPaths, failPaths, test)
      case n =>
        if (DEBUG) { print(" > 1 pred "); preds.foreach(p => print(s" BB${p.getNumber()}")); println }
        val p = instrPaths.head
        val blk = p.blk
        val phis = p.blk.iteratePhis().toIterable

        // push all paths up to the join
        val initCallStackSize = p.callStackSize
        val (prunedCFG, predList) =
          if (Options.SOUND_EXCEPTIONS) (cfg, preds)
          else {
            val prunedCFG = ExceptionPrunedCFG.make(cfg)
            if (prunedCFG.getNumberOfNodes() == 0) (cfg, preds)
            else (prunedCFG, preds.filter(blk => prunedCFG.containsNode(blk)))
          }
        // this is a weird case that arises with explicitly infinite loops or ony exceptional predecessors
        // refute, since there's no way we ever could have gotten here
        if (predList.isEmpty) (passPaths, failPaths)
        else {
          val domInfo = getDominators(prunedCFG)
          val loopHeader = None//LoopUtil.findRelatedLoopHeader(startBlk, ir)
          val forkMap = getForkMap(blk, predList, instrPaths, phis, domInfo, ir, loopHeader)
          if (!forkMap.isEmpty) {
            if (DEBUG) checkPathMap(forkMap)
            val paths = executeToJoin(blk, predList.reverse, forkMap, domInfo, initCallStackSize, cfg)
            filterFailPaths(paths, passPaths, failPaths, test)
          } else (passPaths, failPaths)
        }
     }
  }
  
  // DEBUG only
  private[executor] def checkPathMap(m : Map[ISSABasicBlock,List[Path]]) : Unit = m.keys.foreach(k => checkPathMap(m, k))
  private[executor] def checkPathMap(m : Map[ISSABasicBlock,List[Path]], k : ISSABasicBlock) : Unit = 
      m(k).foreach(p => assert(p.blk == k, "Path " + p.id + " should have blk " + k + ", but it has " + p.blk))
  
  def getForkMap(blk : ISSABasicBlock, preds : Iterable[ISSABasicBlock], instrPaths : List[Path], 
      phis : Iterable[SSAPhiInstruction], domInfo : Dominators[ISSABasicBlock], ir : IR,
      loopHeader : Option[ISSABasicBlock]) : Map[ISSABasicBlock,List[Path]] =
    // experimental: if goal is a switch, pre-constrain the paths. we could consider using this with if's as well
    if (PRE_CONSTRAIN_SWITCHES) {
      val domGraph = domInfo.getGraph()
      if (!domGraph.containsNode(blk))
        // refuted. this happens when eliminating exceptional control flow makes a node unreachable.
        Map.empty
      else {
        val goalBlk = domInfo.getIdom(blk)
        if (CFGUtil.endsWithSwitchInstr(goalBlk) && instrPaths.forall(p => p.switchConstraintsAdded.add(goalBlk))) {
          val cfg = ir.getControlFlowGraph()
          val switch = goalBlk.getLastInstruction.asInstanceOf[SSASwitchInstruction]
          val defaultBlk = cfg.getBlockForInstruction(switch.getDefault()).asInstanceOf[ISSABasicBlock]
          val switchMap = getSwitchMap(switch, ir)  
          
          def constrainBasedOnSwitchCases(blk : ISSABasicBlock, p : Path) : Boolean = domGraph.containsNode(blk) && {
            switchMap.keys.filter(k => CFGUtil.isReachableFrom(blk, cfg.getBasicBlock(k), cfg)) match {
              case keys if keys.isEmpty => // default case
                if (blk == goalBlk || domInfo.isDominatedBy(blk, defaultBlk))
                  switchMap.values.flatten.forall(cond => p.addConstraintFromSwitch(cond, tf, negated = true))
                else {
                  if (DEBUG) sys.error(s"Couldn't find constraining instr for $blk default is $defaultBlk switch blk is $goalBlk ir $ir")
                  true
                }
              case keys =>
                tf.constrainBasedOnSwitchCases(keys.flatMap(k => switchMap(k)), p.qry, p.node) // normal switch case
            }
          }
          
          getForkMapInternal(preds, instrPaths, phis, loopHeader, constrainBasedOnSwitchCases)
        } else getForkMapInternal(preds, instrPaths, phis, loopHeader)
      }
    } else getForkMapInternal(preds, instrPaths, phis, loopHeader)
    
      
  def getForkMapInternal(preds : Iterable[ISSABasicBlock], instrPaths : List[Path], 
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
            /*loopHeader match {
              case Some(loopHeader) =>
                newP.dropLoopProduceableConstraints(loopHeader)
                //if (loopInvMap.pathEntailsInv((newP.node, pred, loopHeader), newP)) {
                if (loopInvMap.pathEntailsInv((pred, newP.callStack.stack.map(f => f.node)), newP)) {
                  //println("refuted by loopInvMap")
                  paths 
                } else {
                  //println("LoopInvMap doesn't entail " + newP)
                  newP :: paths
                }
              case None =>                
                newP :: paths                
            }*/
            newP :: paths
          } else paths // refuted by executing phi
        })
      })
    }
  }
    
  // TMP!
  def ppBlocks(blocks : Iterable[ISSABasicBlock]) : Unit = { blocks.foreach(b => print(" BB" + b.getNumber())); println }  
  def logMethodAndTime(method : String) : Unit = println(s"#$method at ${timekeeper.curTimeSeconds}")
  
  // this is by far the most complicated and delicate code in the symbolic executor -- be careful
  def executeToJoin(node : ISSABasicBlock, worklist : List[ISSABasicBlock], pathMap : Map[ISSABasicBlock,List[Path]], 
                    domInfo : Dominators[ISSABasicBlock], initCallStackSize : Int, cfg : SSACFG) : List[Path] = {
    if (TRACE) logMethodAndTime("executeToJoin")
    val domGraph = domInfo.getGraph()
    val filteredWorklist = worklist.filter(node => domGraph.containsNode(node))
    val goal = domInfo.getIdom(node)

    // we assume the nodes in worklist are unique and that they are arranged in descending order by number (or
    // accordingly, depth in the CFG) our objective is to push each node in preds up to goal, the immediate dominator of
    // node while performing as many joins as possible
    @annotation.tailrec
    def getJoinsRec(worklist : List[ISSABasicBlock],
                    pathMap : Map[ISSABasicBlock,List[Path]]) : Map[ISSABasicBlock,List[Path]] = worklist match {
      case node :: worklist =>
        assert(node != goal, s"node is goal $node")
        val join = if (domGraph.containsNode(node)) domInfo.getIdom(node) else null

        if (join == null) {   
          // this can happen when we are trying to go backward from a catch block. we ignore this path
          // because we assume thrown exceptions are never caught. this is, of course, unsound, but
          // for now we seek only to be sound modulo exceptions
          if (DEBUG) println(s"skipping path from $node to $goal because we don't follow exceptional edges")
          getJoinsRec(worklist, pathMap)          
        } else {
          // one each call to getJoinsRec, we should push the path at pathMap(node) through all blocks up to (but not
          // including) join
          assert (join != node)
          if (DEBUG) checkPathMap(pathMap, node)
          val (paths, newWorklist) = 
            if (join == goal)
              (executeUntilJoin(pathMap(node), join, initCallStackSize, cfg, pathMap.getOrElse(join, Nil)), worklist)
            else worklist match { // try to match with join of next node
              case nextNode :: worklist =>
                if (join == nextNode) {  
                  // need to execute paths at node up to join, then merge them with paths already at join
                  val paths = executeUntilJoin(pathMap(node), join, initCallStackSize, cfg, pathMap(join))
                  (mergeAtJoin(paths, join, cfg), join :: worklist)
                } else if (domInfo.isDominatedBy(nextNode, join)) {
                  if (DEBUG) checkPathMap(pathMap, nextNode)
                  // TODO: problem: what if there's more than one nextNode? we'll merge too aggressively
                  // we can execute until we reach join on the paths at both node and nextNode
                  val combinedPaths = pathMap(node).foldLeft (pathMap(nextNode)) ((lst, p) => p :: lst)
                  val paths =
                    executeUntilJoin(combinedPaths, join, initCallStackSize, cfg, pathMap.getOrElse(join, Nil))
                  // if the nextNode is the *last* item in the worklist with the same join as the current node, we can
                  // merge the two otherwise, we'll delay the join until later
                  if (worklist.forall(node => !domInfo.isDominatedBy(node, join))) {
                    (mergeAtJoin(paths, join, cfg), join :: worklist)     
                  } else (paths, worklist)
                } else 
                  (executeUntilJoin(pathMap(node), join, initCallStackSize, cfg, pathMap.getOrElse(join, Nil)),
                   join :: nextNode :: worklist)
              case Nil => 
                (executeUntilJoin(pathMap(node), join, initCallStackSize, cfg, pathMap.getOrElse(join, Nil)),
                 List(join))
          }   
          // remove paths now at join from paths at node
          val nodePaths = pathMap(node).filter(p => paths.forall(p2 => p.id != p2.id))
          getJoinsRec(newWorklist, pathMap + (join -> paths, node -> nodePaths)) 
        }
      case Nil => pathMap
    }     
    val curJoinCount = if (DEBUG) { joinCount += 1; joinCount } else 0 // debug only
    if (DEBUG) { 
      println(s"$curJoinCount executing all paths to join BB${goal.getNumber()} from node BB${node.getNumber()} initCallStackSize $initCallStackSize")
    }    
    
    val nowAtGoal = getJoinsRec(filteredWorklist.filterNot(b => b == goal), pathMap).getOrElse(goal, Nil)
    if (DEBUG) println(s"$curJoinCount completed join at $goal have ${nowAtGoal.size} paths before merging")
    mergeAtJoin(nowAtGoal, goal, cfg)
  } 
  
  var joinCount = 0
  
  /** keep executing all paths in @param paths until they hit @param join; return the result of execution */
  def executeUntilJoin(paths : List[Path], join : WalaBlock, initCallStackSize : Int, cfg : SSACFG,
                       failPaths : List[Path] = List.empty[Path]) : List[Path] =
    executeBackwardWhile(paths, p => p.blk != join || p.callStackSize != initCallStackSize, failPaths)
  
  // TODO: cache this?
  def getSwitchMap(switchInstr : SSASwitchInstruction, ir : IR) : Map[Int,List[SSAConditionalBranchInstruction]] = {
    val tbl = ir.getSymbolTable
    val cfg = ir.getControlFlowGraph
    val matched = switchInstr.getUse(0)
    val casesAndLabels = switchInstr.getCasesAndLabels
    val indices = casesAndLabels.indices
    //val default = cfg.getBlockForInstruction(switchInstr.getDefault()).getNumber() -> List.empty[SSAConditionalBranchInstruction]
    // meaning of casesAndLabels: case switched == casesAndLabels[i] : jump to block casesAndLabels[i + 1]  
    // list of (ConditionalInstr, target Block) pairs corresponding to the switch cases
    indices.foldLeft (Map.empty[Int,List[SSAConditionalBranchInstruction]]) ((map, index) =>  
      // the Java compiler sometimes fills in middle of jump table with dummy cases that transition to default block.
      // we don't translate these cases.
      if (index % 2 == 0 && casesAndLabels(index + 1) != switchInstr.getDefault()) {
        val (_case, target) = (casesAndLabels(index), cfg.getBlockForInstruction(casesAndLabels(index + 1)).getNumber())
        // check for blocks we've already translated so we can group cases
        val cond = new SSAConditionalBranchInstruction(index, EQ, TypeReference.Int, matched, tbl.getConstant(_case), -1)
        map + (target -> (cond :: map.getOrElse(target, List.empty[SSAConditionalBranchInstruction])))
      } else map
    )
  }
  
  def handleSwitch(paths : List[Path], switch : SSASwitchInstruction, switchBlk : ISSABasicBlock, cfg : SSACFG) : List[Path] =
    if (PRE_CONSTRAIN_SWITCHES &&
        paths.exists(p => p.switchConstraintsAdded.contains(switchBlk))) {
      paths.foreach(p => p.switchConstraintsAdded.remove(switchBlk))
      paths
    } else {
       if (TRACE) logMethodAndTime("handleSwitch")
     // if (paths.toSet.size == 1) println("switch: got reduction to 1 from " + paths.size)//List(paths.head) // switch not relevant -- continue on single path
      //else {
        val defaultNum = cfg.getBlockForInstruction(switch.getDefault()).getNumber()
        if (DEBUG) {
          val pSet = paths.toSet
          if (paths.size != pSet.size) println("got reduction to " + pSet.size + " down from " + paths.size + " by switching to set")
        }
        val switchMap = getSwitchMap(switch, paths.head.node.getIR())
        paths.foldLeft (List.empty[Path]) ((lst, p) => {
          val lastBlkNum = cfg.getNumber(p.lastBlk)
          if (lastBlkNum == defaultNum) {
            val copy = p.deepCopy
            // if we came from default block, need to add negation of all other cases
            if (switchMap.values.flatten.forall(cond => copy.addConstraintFromSwitch(cond, tf, negated = true))) copy :: lst
            else lst // refuted by adding switch constraint
          } else {
            assert (switchMap.containsKey(lastBlkNum),
                    s"switchMap $switchMap does not have an entry for $lastBlkNum ir ${p.node.getIR()}")
            // otherwise, fork a case for each possible value that could have sent us to this block
            switchMap(lastBlkNum).foldLeft (lst) ((lst, cond) => {
              val copy = p.deepCopy
              if (copy.addConstraintFromSwitch(cond, tf)) copy :: lst
              else lst // refuted by adding switch constraint
            })
          }
        })
    //}
  }
    
  /** merge all paths in @param joinPaths that have reached block @param join, adding path conditions if appropriate
   *  @return paths that have been pushed through the conditional branch instruction in @param join, but no further */
  def mergeAtJoin(joinPaths : List[Path], join : WalaBlock, cfg : SSACFG) : List[Path] = {
    if (DEBUG) println("merging at join " + join + " with " + joinPaths.size + " paths")
    //if (joinPaths.isEmpty) failPaths
    joinPaths.foreach(p =>
      assert(p.blk == join, " path " + p + " has current block " + p.blk + " should have " + join + " ir " + joinPaths.head.node.getIR()))      
    
    if (joinPaths.isEmpty) joinPaths
    else {
      if (CFGUtil.endsWithSwitchInstr(join)) {      
        // TODO: avoid adding constraints if all paths are the same?
        val switch = join.getLastInstruction.asInstanceOf[SSASwitchInstruction]
        val joined = handleSwitch(joinPaths, switch, join, cfg)
        val preSwitchIndex = join.asInstanceOf[SSACFG#BasicBlock].getAllInstructions().size - 2          
        joined.foreach(p => p.setIndex(preSwitchIndex)) // set to instruction before the switch
        //MinSet.make(joined).toList // this is quadratic in the size of joined. potentially very bad
        joined
      } else {
        
        def mergeRedundantPaths(paths : List[Path]) : List[Path] = {
           /*if (DEBUG) {
           val set = paths.toSet
           val minset = MinSet.make(paths)
           if (set.size < paths.size || minset.size < paths.size) {
             println("original " + paths.size + " set " + set.size + " minset " + minset.size)
           }
          }*/
          
          // MinSet.make() is worst-case quadratic and uses an SMT solver to check logical implication. it *really* helps prune 
          // redundant paths when the size of combined is small, but is absurdly expensive when the size of combined is large. 
          // we try to trade off appropriately here, but this could certainly be evaluated and tuned better
          if (paths.size < 10) MinSet.make(paths).toList
          else paths // do .toSet?
        }
        
        val joinSuccs = CFGUtil.getSuccessors(join, cfg)                        
        if (joinSuccs.size == 2) {         
          val cond = join.getLastInstruction.asInstanceOf[SSAConditionalBranchInstruction]   
          // first succ in joinSuccs is the then branch, second succ is the else branch
          val (thenPaths, elsePaths) = joinPaths.partition(p => 
            if (p.lastBlk == joinSuccs(0)) true 
            else { assert (p.lastBlk == joinSuccs(1), "expecting last blk to be " + joinSuccs(1) + " but it's " + p.lastBlk); false })
          val combined = mergeBranches(cond, thenPaths, elsePaths)
          val preCondIndex = join.asInstanceOf[SSACFG#BasicBlock].getAllInstructions().size - 2          
          combined.foreach(p => p.setIndex(preCondIndex) )
          mergeRedundantPaths(combined)
        } else mergeRedundantPaths(joinPaths) // non-if, non-switch successor
      }
    }
  }
  
  protected def mergeBranches(cond : SSAConditionalBranchInstruction, thenPaths : List[Path], elsePaths : List[Path]) : List[Path] = 
    // TODO: implement implication merging in then and else path via MinPathSet
    (thenPaths.isEmpty, elsePaths.isEmpty) match {
      case (false, false) => // feasible paths on both sides
        //println("feasible paths on both sides")
        // get paths common to both sides; don't need to add path constraints for these
        val sharedPaths = thenPaths.intersect(elsePaths)
        val sharedPathsSet = sharedPaths.toSet
        //println("SHARED PATHS: "); sharedPathsSet.foreach(println)
        // add path constraints to then and else branches  
        def joinPaths(paths : List[Path], branchPaths : List[Path], trueCond : Boolean) : List[Path] =
          branchPaths.foldLeft (paths) ((paths, path) => 
            if (!sharedPathsSet.contains(path) && path.addConstraintFromConditional(cond, trueCond, tf)) path :: paths
            else paths)
        
        val thenPathsFiltered = joinPaths(sharedPaths, thenPaths, true)
        joinPaths(thenPathsFiltered, elsePaths, false)        
      case (true, true) => Nil // no feasible paths
      case (false, true) => // only then paths feasible
        thenPaths.filter (path => path.addConstraintFromConditional(cond, isThenBranch = true, tf))
      case (true, false) => // only else paths feasible
        elsePaths.filter (path => path.addConstraintFromConditional(cond, isThenBranch = false, tf))
    }
  
  final def executeBackwardWhile(paths : List[Path], test : Path => Boolean = Util.RET_TRUE, failPaths : List[Path] = List.empty[Path]) : List[Path] = {
    // _ because executeBackwardWhileHelper only returns here when passPaths is empty
    val (_, newFailPaths) = executeBackwardWhileHelper(paths, failPaths, test) 
    newFailPaths
  }
  
  var last : CGNode = null
  @annotation.tailrec
  final def executeBackwardWhileHelper(passPaths : List[Path], failPaths : List[Path], test : Path => Boolean) : (List[Path], List[Path]) = 
    passPaths match {
      case path :: rest =>
        checkTimeout

        if (DEBUG) {
          println("executing path " + path + " blk " + path.blk + " index " + path.index + " in method " + ClassUtil.pretty(path.node))
          println("source line " + path.qry.curSourceLine)
          assert (rest.forall(p => p.id != path.id), " path " + path + " occurs twice!")
        }        
        
        val (newPassPaths, newFailPaths) = executeBackwardIntraproceduralWhile(path, rest, failPaths, test)
        assert(newFailPaths.size >= failPaths.size && newPassPaths.size >= rest.size, "dropped path on the floor!")
        executeBackwardWhileHelper(newPassPaths, newFailPaths, test)
      case Nil => (Nil, failPaths)
    }
  
  def checkTimeout() : Unit = if (timekeeper.curTimeSeconds > Options.TIMEOUT) {
    println(s"TIMEOUT: budget ${Options.TIMEOUT} exceeded: took ${timekeeper.curTimeSeconds}")
    throw BudgetExceededException
  }
  
  def cleanup(oldInvMaps : Option[List[InvariantMap[_]]]) : Unit = {
    timekeeper.stop
    timekeeper.clear
    domCache.clear
    // can't get rid of this until we get rid of Thresher's loop-finding functionality
    edu.colorado.thresher.core.WALACFGUtil.clearCaches()

    if(SAVE_INVARIANT_MAPS) {
      oldInvMaps match {
        case Some(oldInvMaps) => resetInvariantMaps(oldInvMaps)
        case None => () // got a refutation, can keep the new maps
      }
    } else clearInvariantMaps
  }     
    
  override def executeBackward(qry : Qry) : Boolean = {
    val pathsAtEntry = executeBackward(qry, None)
    pathsAtEntry == null || pathsAtEntry.exists(p => p.foundWitness)
  }

  override def executeBackward(qry : Qry, test : Option[Path => Boolean]) : Iterable[Path] = {
    if (PRINT_IR) println("starting in " + qry.node.getIR())
    timekeeper.start
    val oldInvMaps = if (SAVE_INVARIANT_MAPS) Some(this.cloneInvariantMaps) else None
    val result = try {             
      val startPath = List(new Path(qry))
      test match {
        case Some(test) => executeBackwardWhile(startPath, test)
        case None => executeBackwardWhile(startPath, Util.RET_TRUE)
      }      
    } catch {
      case WitnessFoundException =>
        println("Witness found via exception")
        null // TODO: this is a hack. find something reasonable to do here
      case BudgetExceededException =>
        println("Exceeded timeout of " + Options.TIMEOUT + " seconds. Giving up.")
        null // TODO: this is a hack. find something reasonable to do here
      case e : Throwable =>
        qry.dispose
        cleanup(oldInvMaps)
        throw e
    }
    qry.dispose
    cleanup(oldInvMaps)
    result
  }
}