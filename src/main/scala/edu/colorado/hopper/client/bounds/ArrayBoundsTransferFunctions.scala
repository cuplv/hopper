package edu.colorado.hopper.client.bounds

import scala.collection.JavaConversions._
import edu.colorado.hopper.executor.TransferFunctions
import com.ibm.wala.ipa.callgraph.CallGraph
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ipa.callgraph.propagation.HeapModel
import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.util.intset.OrdinalSet
import com.ibm.wala.ipa.callgraph.propagation.PointerKey
import edu.colorado.hopper.client.WalaAnalysisResults
import edu.colorado.hopper.state.Qry
import com.ibm.wala.ssa.SSAInstruction
import edu.colorado.hopper.util.Util
import com.ibm.wala.ssa.SSAInvokeInstruction
import com.ibm.wala.ssa.SSAPhiInstruction
import ArrayBoundsTransferFunctions._
import edu.colorado.thresher.core.Options
import com.ibm.wala.ssa.ISSABasicBlock
import com.ibm.wala.ssa.SSACFG

object ArrayBoundsTransferFunctions {
  private val DEBUG = Options.SCALA_DEBUG
}

class ArrayBoundsTransferFunctions(walaRes : WalaAnalysisResults) 
  extends TransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha, walaRes.modRef) {
  
  override def dropConstraintsFromInstructions(i : Iterable[SSAInstruction], n : CGNode, qry : Qry, 
                                               callee : Option[CGNode] = None, loopDrop : Boolean = false) : Unit = {
    require(Util.implies(callee.isDefined, i.forall(i => i.isInstanceOf[SSAInvokeInstruction])))
    // important to do this first; otherwise we may unsoundly assume a local binding holds when it can in fact be reassigned in a loop
    // qry.node check is because we only need to drop local constraints for the current node (not for callees, 
    // because we won't have any)
    if (qry.node == n) {
      val dropInstrs = if (loopDrop) {
        val changingDefs = getChangingDefs(i)
        i.filter(i => changingDefs.contains(i.getDef()))
      } else i
      // purposely turn off problem-causing loopDrop
      dropInstrs.foreach(i => dropLocalConstraintsFromInstruction(i, qry, loopDrop = false)) 
    }
    // purposely turn off problem-causing loopDrop
    i.foreach(i => dropHeapConstraintsFromInstruction(i, n, qry, modRef, loopDrop = false, callee))  
  }
  
  override def dropLoopWriteableConstraints(qry : Qry, loopHead : ISSABasicBlock, n : CGNode) : Unit = {
    val loopInstrs = edu.colorado.thresher.core.WALACFGUtil.getInstructionsInLoop(loopHead.asInstanceOf[SSACFG#BasicBlock], n.getIR()).toSet
    dropConstraintsFromInstructions(loopInstrs, n, qry, callee = None, loopDrop = true)
  }
  
  // get the value numbers of all def's that may assign to a value that changes in the loop
  def getChangingDefs(instrs : Iterable[SSAInstruction]) : Set[Int] = {
    val (defs, phiUses) = instrs.foldLeft (Set.empty[Int], Map.empty[Int,Seq[Int]]) ((pair, i) => {
      val (defs, phiUses) = pair
      i match {
        case i : SSAPhiInstruction =>          
          (defs, phiUses + (i.getDef() -> (0 to i.getNumberOfUses() - 1).map(j => i.getUse(j))))
        case i if i.hasDef() => (defs + i.getDef(), phiUses)
        case _ => pair
      }
    })
    
    // we only want to count a phi use as a def if it can assign to something that's changing in the loop
    // thus, only count a phi def as a def if it assigns to another *non-phi* def
    @annotation.tailrec
    def addPhiUsesRec(defs : Set[Int], phiUses : Map[Int,Seq[Int]], misses : Int = 0) : Set[Int] = phiUses match {
      case phiUses if !phiUses.isEmpty =>
        val (key, valu) = phiUses.head
        if (valu.exists(use => defs.contains(use))) {
          addPhiUsesRec(defs + key, phiUses - key, 0)
        } else {
          val newMisses = misses + 1
          if (newMisses == phiUses.size) defs // we've looked at everything and found no phi uses that are also defs
          else addPhiUsesRec(defs, phiUses, newMisses)
        }
      case _ => defs
    }
    // get the list of defs that may change in a loop
    addPhiUsesRec(defs, phiUses)
  }    
}