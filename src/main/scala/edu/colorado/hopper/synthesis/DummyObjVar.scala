package edu.colorado.hopper.synthesis

import edu.colorado.hopper.state.ObjVar
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey
import com.ibm.wala.types.TypeReference
import com.ibm.wala.classLoader.IClass
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.classLoader.NewSiteReference
import com.ibm.wala.ipa.callgraph.CallGraph
import edu.colorado.hopper.util.ClassUtil

object DummyObjVar {
  
  def makeDummyObjVarFromType(typ : TypeReference, cha : IClassHierarchy) : DummyObjVar = {
    val clazz = cha.lookupClass(typ)
    val dummyKey = new InstanceKey {      
      override def getConcreteType : IClass = clazz      
      override def getCreationSites(cg : CallGraph) : java.util.Iterator[com.ibm.wala.util.collections.Pair[CGNode,NewSiteReference]] = null
      override def toString : String = "DUMMY_" + ClassUtil.pretty(clazz)
    }
    new DummyObjVar(typ, Set(dummyKey))
  }
}

/** ObjVar created in response to an empty points-to set */
class DummyObjVar(typ : TypeReference, rgn : Set[InstanceKey]) extends ObjVar(rgn) {}