package edu.colorado.hopper.synthesis

import com.ibm.wala.classLoader.{IClass, IMethod}
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.types.TypeReference
import edu.colorado.thresher.core.SharedAllocationEntrypoint

 // WALA refuses to treat allocations of interface types as allocation sites, which can lead to wonky results in the points-to analysis
// typically, we can overcome this by choosing all implementations of the interface type in scope, but sometimes there aren't any
// in this case, we can use this entrypoint to generate a dummy implementation of the interface type that WALA will treat as an allocation
class DummyImplGeneratingEntrypoint(m : IMethod, cha : IClassHierarchy, useExistingImpls : Boolean) extends SharedAllocationEntrypoint(m, cha) {
  
  override def chooseAllImplementors(iface : IClass, cha : IClassHierarchy) : Array[TypeReference] = {    
    val impls = if (useExistingImpls) super.chooseAllImplementors(iface, cha) else Array.empty[TypeReference]
    if (impls == null || impls.length == 0) {
      assert(iface.isInterface(), s"Expected interface type but found $iface")      
      val dummyImpl = DummyIClass.findOrCreateDummySubclass(iface, cha) 
      assert(cha.lookupClass(dummyImpl.getReference()) != null, s"Failed to fund dummyImpl $dummyImpl during class lookup")
      Array(dummyImpl.getReference())
    } else impls  
  } 
  
  override def chooseAllConcreteSubClasses(klass : IClass, cha : IClassHierarchy) : Array[TypeReference] = {
    val impls = super.chooseAllConcreteSubClasses(klass, cha)
    assert(impls != null && impls.length != 0, "No concrete subs for " + klass)
    impls    
  }  
  
 
  

}