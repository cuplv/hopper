package edu.colorado.hopper.synthesis

import com.ibm.wala.classLoader.IMethod
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.types.MethodReference
import edu.colorado.hopper.state.InstanceFld
import edu.colorado.walautil.ClassUtil


object InterfaceMethodField {
  def makeInterfaceMethodField(m : MethodReference, cha : IClassHierarchy) : InterfaceMethodField = 
    new InterfaceMethodField(cha.resolveMethod(m))
}

/** field representing a constraint on an interface method */
// TODO: ok to pass null here, or do we need to generate a dummy IField to avoid exceptions?
class InterfaceMethodField(val method : IMethod) extends InstanceFld(null) {  
  override def equals(o : Any) : Boolean = o match {
    case o : InterfaceMethodField => method == o.method
    case _ => false
  }  
  override def hashCode : Int = method.hashCode()
  override def toString : String = "{"+ ClassUtil.pretty(method) + "}"
}