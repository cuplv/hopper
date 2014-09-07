package edu.colorado.scwala.synthesis

import scala.collection.JavaConversions._
import edu.colorado.thresher.core.SharedAllocationEntrypoint
import com.ibm.wala.classLoader.IMethod
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.classLoader.IClass
import com.ibm.wala.types.TypeReference
import com.ibm.wala.util.strings.Atom
import com.ibm.wala.types.TypeName
import com.ibm.wala.classLoader.IClassLoader
import com.ibm.wala.types.annotations.Annotation
import edu.colorado.scwala.util.Util
import com.ibm.wala.types.Selector
import java.io.InputStream
import com.ibm.wala.classLoader.IField
import com.ibm.wala.types.Descriptor
import com.ibm.wala.types.MethodReference
import com.ibm.wala.classLoader.IBytecodeMethod
import com.ibm.wala.shrikeBT.IndirectionData
import com.ibm.wala.shrikeBT.IInstruction
import com.ibm.wala.classLoader.CallSiteReference
import com.ibm.wala.shrikeBT.ExceptionHandler
import com.ibm.wala.classLoader.SyntheticMethod
import com.ibm.wala.ipa.callgraph.Context
import com.ibm.wala.ssa.SSAOptions
import com.ibm.wala.ssa.SSAInstruction
import com.ibm.wala.ssa.IR
import edu.colorado.scwala.util.IRUtil
import com.ibm.wala.classLoader.NewSiteReference
import com.ibm.wala.classLoader.ProgramCounter
import com.ibm.wala.ipa.summaries.SyntheticIR
import com.ibm.wala.ipa.callgraph.impl.Everywhere

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