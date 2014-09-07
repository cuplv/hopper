package edu.colorado.scwala.state

import com.ibm.wala.ipa.callgraph.propagation.LocalPointerKey
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey
import edu.colorado.scwala.util.Util
import com.ibm.wala.classLoader.IField
import com.ibm.wala.ipa.callgraph.propagation.ReturnValueKey
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey

trait PtEdge {
  def src : Any // TODO: stronger typing here
  def snk : Val
  def |=(other : PtEdge) : Boolean
  def getVals : Set[Val]
}

case class LocalPtEdge(val src : StackVar, val snk : Val) extends PtEdge {
  override def |=(other : PtEdge) = src == other.src && (snk |= other.snk)
  override def getVals : Set[Val] = Set(snk)
  override def clone : LocalPtEdge = this
  override def hashCode : Int = Util.makeHash(List(src, snk))
  override def equals(other : Any) : Boolean = other match {
    case e : LocalPtEdge => this.src == e.src && this.snk == e.snk
    case _ => false
  }
  override def toString : String = src.toString() + " -> " + snk.toString()
}

abstract class HeapPtEdge(val src : HeapVar, val fld : Fld, val snk : Val) extends PtEdge {
  def isClinitEdge : Boolean = src.isClinitVar && { snk match {
    case o@ObjVar(_) => o.isClinitVar
    case _ => true
  }}

  override def clone : HeapPtEdge = this
  override def hashCode : Int = Util.makeHash(List(src, fld, snk))
  override def equals(other : Any) : Boolean = other match {
    case e : HeapPtEdge => this.src == e.src && this.fld == e.fld && this.snk == e.snk
    case _ => false
  }
  override def toString : String = src.toString() + "." + fld.toString() + " -> " + snk.toString()
}
case class ObjPtEdge(override val src : ObjVar, override val fld : InstanceFld, override val snk : Val) extends HeapPtEdge(src, fld, snk) {
  override def getVals : Set[Val] = Set(src, snk)
  override def |=(other : PtEdge) : Boolean = other match {
    case e@ObjPtEdge(eSrc, eFld, eSnk) => fld == eFld && (src |= e.src) && (snk |= e.snk)
    case _ => false
  }
} 
case class StaticPtEdge(override val src : ClassVar, override val fld : StaticFld, override val snk : Val) extends HeapPtEdge(src, fld, snk) {
  override def getVals : Set[Val] = Set(snk)
  override def |=(other : PtEdge) : Boolean = other match {
    case e@StaticPtEdge(eSrc, eFld, eSnk) => src == eSrc && fld == eFld && (snk |= e.snk)
    case _ => false
  }
}
case class ArrayPtEdge(override val src : ObjVar, override val fld : ArrayFld, override val snk : Val) extends HeapPtEdge(src, fld, snk) {
  override def getVals : Set[Val] = Set(src, snk)
  override def |=(other : PtEdge) : Boolean = other match {
    case e@ArrayPtEdge(eSrc, eFld, eSnk) => fld == eFld && (src |= e.src) && (snk |= e.snk)
    case _ => false
  }
}

object PtEdge {  
  
  def make(src : HeapVar, fld : IField, snk : Val) : HeapPtEdge = make(src, InstanceFld(fld), snk)
  
  def make(src : HeapVar, fld : Fld, snk : Val) : HeapPtEdge = (src, fld) match {
    case (src@ObjVar(_), fld@InstanceFld(_)) => ObjPtEdge(src, fld, snk)
    case (src@ClassVar(_), fld@StaticFld(_)) => StaticPtEdge(src, fld, snk)
    case (src@ObjVar(_), fld@ArrayFld(_, _, _)) => ArrayPtEdge(src, fld, snk)
    case _ => sys.error("Bad HeapPtEdge components " + src + " . " + fld + " -> " + snk + 
                        " Classes " + src.getClass + " " + fld.getClass + " " + snk.getClass)
  }
  
  def make(src : StaticFieldKey, snk : Val) : HeapPtEdge = StaticPtEdge(ClassVar(src.getField().getDeclaringClass()), StaticFld(src), snk)
  def make(src : StackVar, snk : Val) : LocalPtEdge = LocalPtEdge(src, snk)
  def make(src : LocalPointerKey, snk : Val) : LocalPtEdge = make(LocalVar(src), snk)
  def make(src : ReturnValueKey, snk : Val) : LocalPtEdge = make(ReturnVar(src), snk)   
}