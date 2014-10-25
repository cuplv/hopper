package edu.colorado.hopper.synthesis

import scala.collection.JavaConversions.asScalaSet
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ssa.SSAInvokeInstruction
import edu.colorado.hopper.executor.UnstructuredSymbolicExecutor
import edu.colorado.hopper.state.Path
import edu.colorado.hopper.util.ClassUtil
import edu.colorado.hopper.executor.DefaultSymbolicExecutor

case class InvokeSynthesizerException(path : Path) extends Exception

class SynthesisSymbolicExecutor(tf : SynthesisTransferFunctions) extends DefaultSymbolicExecutor(tf) {  
  
  // one of the biggest sources of distraction of Thresher is chasing down pure constraints on procedure return 
  // values that it cannot hope to prove (e.g., hashCode(), indexOf()). for synthesis, we implement an
  // optimization that chooses to drop constraints on function return values if (a) the return value is
  // a primitive type and (b) the method body is "complicated" (i.e., not just "return 5")
  
  def shouldSkipDueToPrimitiveReturnValue(i : SSAInvokeInstruction, callees : Set[CGNode]) : Boolean = {
    val TOO_MANY_INSTRUCTIONS = 15 // completely arbitrary; change if needed
    i.getDeclaredTarget().getReturnType().isPrimitiveType() &&
    // proxy for "method body complicated"
    callees.exists(n => n.getIR() != null && n.getIR().getInstructions().length > TOO_MANY_INSTRUCTIONS) 
  }
  
  override def enterCallee(paths : List[Path], i : SSAInvokeInstruction) : (List[Path], List[Path]) = {
    val caller = paths.head.node    
    val callees = cg.getPossibleTargets(caller, i.getCallSite())
    // TODO: decision point here if we just do this when callees are empty, we are limiting our synthesis to the case where there are *no*
    // implementations of the interface that can flow to this call site. if we want to be more aggressive with our synthesis, we can 
    // uncomment the two lines below and thus allow synthesis for interface types that do have concrete implementations flowing to this
    // call site
    // val declaringClass = cha.lookupClass(i.getCallSite().getDeclaredTarget().getDeclaringClass())
    //if (declaringClass.isInterface() || callees.isEmpty()) {
    if (callees.isEmpty() || (callees.size() == 1 && callees.iterator().next().getMethod().isInstanceOf[DummyIMethod])) {
      // add constraints on the implementation of the interface method
      paths.foreach(p => tf.visitInterfaceMethod(i, p.qry, p.node))
      (Nil, paths)
    } else {
      // drop return value constraints if it seems like it will improve performance without hurting precision
      if (shouldSkipDueToPrimitiveReturnValue(i, callees.toSet)) paths.foreach(p => p.dropReturnValueConstraints(i, caller, tf))
      super.enterCallee(paths, i)
    } 
    
  }
  
  override def returnFromCall(p : Path) : Iterable[Path] = {
    val callee = p.callStack.top.node // get rid of current stack frame

    if (p.callStackSize == 1 && callee.getMethod().isPublic()) {
      // at function boundary of public method; we can call this method from our harness and try to make the assertion fail
      println("Reached public entrypoint " + ClassUtil.pretty(callee))      
      throw new InvokeSynthesizerException(p) // try to invoke the synthesizer
    }
    else super.returnFromCall(p) // otherwise, continue execution as normal
  }
  
}