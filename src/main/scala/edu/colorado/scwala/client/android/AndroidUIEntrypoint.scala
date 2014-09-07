package edu.colorado.scwala.client.android

import edu.colorado.thresher.core.SharedAllocationEntrypoint
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.classLoader.IMethod
import com.ibm.wala.ipa.callgraph.impl.AbstractRootMethod
import com.ibm.wala.types.TypeReference
import com.ibm.wala.classLoader.CallSiteReference
import com.ibm.wala.shrikeBT.IInvokeInstruction
import com.ibm.wala.types.MethodReference

// want entrypoint that calls findViewById to create a View instead of allocating a fresh View
class AndroidUIEntrypoint(method : IMethod, cha : IClassHierarchy, val stubMap : Map[TypeReference,MethodReference]) extends SharedAllocationEntrypoint(method, cha) {
  
  override def makeArgument(m : AbstractRootMethod, i : Int) : Int = {
    stubMap.get(method.getParameterType(i)) match {
      case Some(stubMethod) =>
        val callSite = CallSiteReference.make(0, stubMethod, IInvokeInstruction.Dispatch.STATIC)
        // TODO: check that none of the parameter types are in the stubMap?
        val params = (0 to stubMethod.getNumberOfParameters() - 1).map(i => getOrCreateCachedArg(stubMethod.getParameterType(i), m))
        val defNum = m.addInvocation(params.toArray, callSite).getDef()
        defNum
      case None => super.makeArgument(m, i) // normal case, delegate
    }       
  }

}