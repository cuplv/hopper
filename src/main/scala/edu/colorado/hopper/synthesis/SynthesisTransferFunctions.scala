package edu.colorado.hopper.synthesis

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.analysis.typeInference.TypeInference
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.callgraph.CallGraph
import com.ibm.wala.ipa.callgraph.propagation.HeapModel
import com.ibm.wala.ipa.callgraph.propagation.LocalPointerKey
import com.ibm.wala.ipa.callgraph.propagation.PointerKey
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ssa.SSAInvokeInstruction
import com.ibm.wala.util.intset.OrdinalSet

import edu.colorado.hopper.executor.TransferFunctions
import edu.colorado.hopper.state.LocalPtEdge
import edu.colorado.hopper.state.PtEdge
import edu.colorado.hopper.state.Qry
import edu.colorado.hopper.state.Var
import edu.colorado.hopper.util.PtUtil

class SynthesisTransferFunctions(cg : CallGraph, hg : HeapGraph, _hm : HeapModel, cha : IClassHierarchy, modRef : java.util.Map[CGNode, OrdinalSet[PointerKey]]) 
  extends TransferFunctions(cg, hg, _hm, cha, modRef) {
  
   // we choose *not* to refute based on empty PT sets
  override def refuteBasedOnEmptyPT(lpk : LocalPointerKey, qry : Qry, n : CGNode) : Boolean = {
    val typeInference = TypeInference.make(n.getIR(), true)
    val typeRef = typeInference.getType(lpk.getValueNumber()).getTypeReference
    qry.addLocalConstraint(PtEdge.make(lpk, DummyObjVar.makeDummyObjVarFromType(typeRef, cha)))
    true 
  }
  
  def visitInterfaceMethod(i : SSAInvokeInstruction, qry : Qry, n : CGNode) : Unit = {
    // TODO: for now, we're be assuming the call is side-effect free. if we want, we can choose to use side effects to satisfy
    // constraints on the reachable heap from method params of the interface method (+ the reachable heap from publicly accessible static fields)
    if (i.hasDef()) getConstraintEdgeForDef(i, qry.localConstraints, n) match {
      case Some(e@LocalPtEdge(_, retvalSnk)) =>
        assert(!i.isStatic(), "Unimp: static calls")
        qry.removeLocalConstraint(e)
        val method = i.getDeclaredTarget()
        val receiver = Var.makeLPK(i.getReceiver(), n, hm)
        val (receiverObj, receiverEdge) = PtUtil.getPt(receiver, qry.localConstraints, hg) match {
          case Some(pair) => pair
          case None => // no points-to set for receiver -- generate an artificial one
            (DummyObjVar.makeDummyObjVarFromType(method.getDeclaringClass(), cha), None)             
        }
        qry.addHeapConstraint(PtEdge.make(receiverObj, InterfaceMethodField.makeInterfaceMethodField(method, cha), retvalSnk))
        if (!receiverEdge.isDefined) qry.addLocalConstraint(PtEdge.make(receiver, receiverObj))
      case None => () // TODO: do side effect stuff here, if desired
    } else () // TODO: do side effect stuff here, if desired    
  }  
}