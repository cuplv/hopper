package edu.colorado.scwala.state

import com.ibm.wala.classLoader.IField
import com.ibm.wala.ipa.callgraph.propagation.ArrayContentsKey
import com.ibm.wala.ipa.callgraph.propagation.HeapModel
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.types.ClassLoaderReference
import com.ibm.wala.types.FieldReference
import com.ibm.wala.types.TypeReference
import edu.colorado.scwala.util.ClassUtil
import com.ibm.wala.ipa.callgraph.propagation.PointerKey
import com.ibm.wala.ipa.callgraph.propagation.InstanceFieldKey
import edu.colorado.scwala.util.Util

sealed trait Fld {
  def isPrimitiveType : Boolean
  def isReferenceType : Boolean = !isPrimitiveType
}
case class InstanceFld(fld : IField) extends Fld { 
  override def isPrimitiveType : Boolean = fld.getFieldTypeReference().isPrimitiveType()  
  override def equals(other : Any) = other match {
    case InstanceFld(f) => fld == f
    case _ => false
  }
  override def hashCode : Int = fld.hashCode()
  override def toString : String = ClassUtil.pretty(fld)
}
// TODO: want an IField or StaticFieldKey here?
case class StaticFld(fld : StaticFieldKey) extends Fld {
  def iFld : IField = fld.getField()
  def isFinal : Boolean = iFld.isFinal()
  override def isPrimitiveType : Boolean = iFld.getFieldTypeReference().isPrimitiveType()  
  override def equals(other : Any) = other match {
    case StaticFld(f) => this.fld == f
    case _ => false
  }
  override def hashCode : Int = fld.hashCode()
  override def toString : String = ClassUtil.pretty(fld.getField())
}
// TODO: is key necessary?
case class ArrayFld(keys : Set[ArrayContentsKey], typ : TypeReference, index : Option[PureVar]) extends Fld {
  def arrayElementType : TypeReference = typ.getArrayElementType()
  override def isPrimitiveType : Boolean = !arrayElementType.isReferenceType()  

  def |=(other : ArrayFld) : Boolean = keys.subsetOf(other.keys) && { other.index match {
    case None => true
    case Some(p) => index.isDefined && (index.get |= p)
    }
  }

  override def equals(other : Any) = other match {
    case ArrayFld(k, t, i) => this.keys == k && this.index == i
    case _ => false
  }
  
  override def hashCode : Int = Util.makeHash(List(keys, typ, index))
    
  override def toString : String = {
    val indexStr = index match {
      case Some(v) => v.toString
      case _ => "_"
    }
    "[" + indexStr + "]" 
  }
}

object Fld {

  def make(k : PointerKey, cha : IClassHierarchy) : Fld = k match {
    case k : InstanceFieldKey => InstanceFld(k.getField)
    case k : ArrayContentsKey => makeArrayFld(Set(k), None, cha) 
    case other => sys.error("Can't make Fld from bad pointer key " + other)
  }
  
  def make(fld : FieldReference, hm : HeapModel, cha : IClassHierarchy) : Fld = {
    val iFld = cha.resolveField(fld)
    if (iFld.isStatic()) makeStaticFld(iFld, hm)
    else InstanceFld(iFld)
  } 
  
  def makeArrayFld(keys : Set[ArrayContentsKey], index : Option[PureVar], cha : IClassHierarchy) : ArrayFld = {
    val arrRefClass = keys.head.getInstanceKey().getConcreteType()
    assert(arrRefClass.getReference().isArrayType())
    // keep the most general type in keys
    val typ = keys.foldLeft (arrRefClass) ((typ, key) => {
      val newTyp = key.getInstanceKey().getConcreteType()
      if (cha.isAssignableFrom(typ, newTyp)) typ else {
        if (cha.isAssignableFrom(newTyp, typ)) newTyp
        else // odd case, incomparable types. go to T (object)
          cha.lookupClass(TypeReference.JavaLangObject)
      }}) 
    ArrayFld(keys, typ.getReference(), index)
  }
  
  def makeSFK(fld : IField, hm : HeapModel) : StaticFieldKey = {
    require(fld.isStatic())
    hm.getPointerKeyForStaticField(fld).asInstanceOf[StaticFieldKey]
  }
    
  def makeStaticFld(fld : IField, hm : HeapModel) : StaticFld = StaticFld(makeSFK(fld, hm))
  
  def isArrayLengthFld(fld : Fld) : Boolean = fld match {
    case InstanceFld(fld) => isArrayLengthFld(fld)
    case _ => false
  }  
  def isArrayLengthFld(fld : IField) : Boolean = isArrayLengthFld(fld.getReference())
  def isArrayLengthFld(fld : FieldReference) : Boolean = fld == ARRAY_LENGTH_IFLD.getReference()      

  private val ARRAY_LENGTH_IFLD = new IField() {
    override def getReference = FieldReference.findOrCreate(ClassLoaderReference.Primordial, "array", "length", "Int");
    override def getFieldTypeReference = getReference.getFieldType()
    override def getName = getReference.getName()
    override def getAnnotations = null
    override def getClassHierarchy = null
    override def getDeclaringClass = null
    override def isFinal = true
    override def isVolatile = false
    override def isStatic = false
    override def isPublic = false
    override def isProtected = false
    override def isPrivate = false
  }
  
  val ARRAY_LENGTH = InstanceFld(ARRAY_LENGTH_IFLD)  
}
