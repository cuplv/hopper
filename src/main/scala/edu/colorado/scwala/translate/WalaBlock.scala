package edu.colorado.scwala.translate

import scala.language.implicitConversions
import com.ibm.wala.ssa.ISSABasicBlock
import com.ibm.wala.ssa.SSACFG
import com.ibm.wala.ssa.SSAInstruction


object WalaBlock {
  type Blk = SSACFG#BasicBlock

  implicit def fromISSABasicBlock(i : ISSABasicBlock) : WalaBlock = new WalaBlock(i)
  implicit def fromWalaBlock(b : WalaBlock) : ISSABasicBlock = b.blk
}
  // need to do this because ISSABasiBlocks use reference equality by default
class WalaBlock(val blk : ISSABasicBlock) {
  override def equals(that : Any) : Boolean = that match {
    case that : ISSABasicBlock => that.getNumber() == this.blk.getNumber()
    case that : WalaBlock => that.blk.getNumber() == this.blk.getNumber()
  }
  
  override def hashCode : Int = this.blk.getNumber()
  
  override def toString : String = "BB" + this.blk.getNumber()
  
  //def getNumber : Int = blk.getNumber()
  //def getLastInstructionIndex : Int = blk.getLastInstructionIndex()
  def getLastInstruction : SSAInstruction = blk.getLastInstruction()
  def size = blk.asInstanceOf[SSACFG#BasicBlock].getAllInstructions().size()
}
 