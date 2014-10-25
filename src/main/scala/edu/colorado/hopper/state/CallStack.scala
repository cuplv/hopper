package edu.colorado.hopper.state

import edu.colorado.hopper.util.Types._
import edu.colorado.hopper.util.ClassUtil
import com.ibm.wala.ipa.callgraph.CGNode
import edu.colorado.hopper.util.Util
import com.ibm.wala.ssa.SSAInstruction
import com.ibm.wala.ssa.ISSABasicBlock
import com.ibm.wala.ssa.SSACFG
import com.ibm.wala.ssa.SSAInvokeInstruction

object CallStackFrame {
  def make(n : CGNode, localConstraints : MSet[LocalPtEdge], callInstr : SSAInvokeInstruction) : CallStackFrame = {
    val exit = n.getIR().getExitBlock()
    new CallStackFrame(n, localConstraints, exit, exit.getLastInstructionIndex(), Some(callInstr))
  }
}

/** mutable call stack frame holding all program loc information 
 *  @param node - CGNode holding method of current frame
 *  @param localConstraints - set of LocalVar -> Val constraints
 *  @param blk - basic block of current program point 
 *  @param index - index into @param blk corresponding to current instr *
 *  @param callInstr - optionally, the invoke instruction that created this stack frame */
class CallStackFrame(val node : CGNode, val localConstraints : MSet[LocalPtEdge], 
                     var blk : ISSABasicBlock, var index : Int, val callInstr : Option[SSAInvokeInstruction] = None) {  

  def curInstr : Option[SSAInstruction] = if (index < 0 || index >= blk.getLastInstructionIndex()) None else
    Some(blk.asInstanceOf[SSACFG#BasicBlock].getAllInstructions().get(index))  
  override def clone : CallStackFrame = new CallStackFrame(node, localConstraints.clone, blk, index, callInstr)
  override def equals(that : Any) : Boolean = that match {
    case s : CallStackFrame => 
      /*println("comparing " + s + " and " + this)
      println("nodes eq? " + (node == s.node ))
      println("blks eq? " + (this.blk == s.blk))
      println("indices eq? " + (this.index == s.index))
      println("locs eq? " + (this.localConstraints == s.localConstraints))
      println(this.localConstraints)
      println(s.localConstraints)*/
      this.node == s.node && this.blk == s.blk && this.index == s.index && this.localConstraints == s.localConstraints
    case _ => false
  }
  override def toString : String = ClassUtil.pretty(node) + " " + blk.toString + " " + index + " call: " + callInstr
  override def hashCode : Int = Util.makeHash(List(node, blk, index))
}

class CallStack(private val _stack : MStack[CallStackFrame] = new MStack[CallStackFrame]) {
  def stack : Iterable[CallStackFrame] = _stack
  def top : CallStackFrame = _stack.top  
  def push(f : CallStackFrame) : Unit = _stack.push(f)
  def pop : CallStackFrame = _stack.pop
  def clear() : Unit = _stack.clear
  def size : Int = _stack.size
  def isEmpty : Boolean = _stack.isEmpty
  
  override def clone : CallStack = // can't use stack.clone because we need to clone each frame as well
    new CallStack(stack.foldRight (new MStack[CallStackFrame]) ((frame, _stack) => _stack.push(frame.clone)))
  override def equals(that : Any) : Boolean = that match {
    case c : CallStack =>
      /*println("sizes are " + c.size + " and " + this.size)
      println("comparing stacks " + c._stack + " and " + this._stack + " eq? ")
      val res = c._stack == this._stack
      println(res)*/
      c._stack == this._stack
    case _ => false
  }
  override def toString : String = _stack.toString
  override def hashCode : Int = Util.makeHash(List(_stack))
}
