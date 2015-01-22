package edu.colorado.hopper.util

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.classLoader.IField
import com.ibm.wala.ipa.callgraph.propagation.{ArrayContentsKey, HeapModel, InstanceFieldKey, InstanceKey, LocalPointerKey, PointerKey}
import com.ibm.wala.ipa.cha.IClassHierarchy
import edu.colorado.hopper.state.{ArrayPtEdge, ClassVar, Fld, HeapPtEdge, LocalPtEdge, ObjPtEdge, ObjVar, Pure, PureVar, StaticFld, Val}
import edu.colorado.walautil.Types.MSet

import scala.collection.JavaConversions.{asScalaIterator, setAsJavaSet}


object PtUtil {
  
  // ==== consulting the heap graph for points-to facts ====
  
  private def getSuccs[T](src : Set[_ <: Object], hg : HeapGraph[InstanceKey]) : Set[T] = src.foldLeft (Set.empty[T]) ((keys, key) =>
    hg.getSuccNodes(key).toIterable.foldLeft (keys) ((keys, key) => keys + key.asInstanceOf[T])) 
      
  def getPtI(i : InstanceKey, fld : IField, hg : HeapGraph[InstanceKey], keys : Set[InstanceKey]) : Set[InstanceKey] =
    hg.getSuccNodes(i).foldLeft (keys) ((keys, key) => key match {
      case f : InstanceFieldKey if f.getField() == fld => hg.getSuccNodes(f).foldLeft (keys) ((keys, key) => keys + key.asInstanceOf[InstanceKey])
      case _ => keys
    })
  
  /** @return InstanceKeys pointed to by @param i through any field */
  def getPt(i : InstanceKey, hg : HeapGraph[InstanceKey]) : Set[InstanceKey] =
    hg.getSuccNodes(i).foldLeft (Set.empty[InstanceKey]) ((s, f) =>
      hg.getSuccNodes(f).foldLeft (s) ((s, i) => i match {
        case i : InstanceKey => s + i
        case _ => s
      })
    )
    
  /** for all i \in @param keys, get instance keys pointed to by i.fld in @param hg */
  def getPtI(keys : Set[InstanceKey], fld : IField, hg : HeapGraph[InstanceKey]) : Set[InstanceKey] =
    keys.foldLeft (Set.empty[InstanceKey]) ((keys, key) => getPtI(key, fld, hg, keys))
    
  /** get instance keys pointed to by @param o through @param fld in @param hg */
  def getPt(o : ObjVar, fld : IField, hg : HeapGraph[InstanceKey]) : Set[InstanceKey] = getPtI(o.rgn, fld, hg)
  
  def getPtA(o : ObjVar, hg : HeapGraph[InstanceKey]) : Set[InstanceKey] = {
    val arrKeys = getSuccs[ArrayContentsKey](o.rgn, hg)
    getSuccs[InstanceKey](arrKeys, hg)
  }
  
  def getPtL(l : LocalPointerKey, fld : IField, hg : HeapGraph[InstanceKey]) : Set[InstanceKey] =
    getPtI(getPt(l, hg), fld, hg) 
  
  def getPt(k : PointerKey, hg : HeapGraph[InstanceKey]) : Set[InstanceKey] =
    hg.getSuccNodes(k).toSet.map((k : Object) => k.asInstanceOf[InstanceKey])
      
  // ==== consulting constraints for points-to facts with a fallback to the heap graph ====
    
  // should only call this if we have a local pointer to obj -- otherwise, should call method that considers possibility of aliasing
  def getPtO(obj : ObjVar, fld : IField, heapConstraints : MSet[HeapPtEdge], hg : HeapGraph[InstanceKey]) : (ObjVar, Option[ObjPtEdge]) = {
    require(fld.getFieldTypeReference().isReferenceType())
    // collectFirst is ok because there can only be one edge of the form o.fld -> _ (else, we have simultaneous pts-to...)
    heapConstraints.collectFirst({ case edg@ObjPtEdge(o, f, _) if obj == o && fld == f.fld => edg }) match {
      case Some(edg) => edg match {
        case edg@ObjPtEdge(_, _, snk@ObjVar(_)) => (snk, Some(edg)) 
        case edg@ObjPtEdge(_, _, _) => sys.error("pure snk")
      }
      case None => 
        val pt = getPt(obj, fld, hg)
        (ObjVar(pt), None)
    }
  }      
  
  def getPtS(fld : IField, heapConstraints : MSet[HeapPtEdge], hm : HeapModel, hg : HeapGraph[InstanceKey]) : Option[(Val,Option[HeapPtEdge])] = {
    val classVar = ClassVar(fld.getDeclaringClass())
    val fldKey = Fld.makeSFK(fld, hm)    
    val staticFld = StaticFld(fldKey)
    heapConstraints.find(edge => edge.src == classVar && edge.fld == staticFld) match {
      case Some(edge) => Some(edge.snk, Some(edge))
      case None => // fld not in heap constraints; need to look up in pts-to graph
       if (fld.getFieldTypeReference().isPrimitiveType()) Some(Pure.makePureVar(fld.getFieldTypeReference()), None) 
        //else ObjVar(getPt(fldKey, hg)), None)
       else getPt(fldKey, hg) match {
         case rgn if rgn.isEmpty => None
         case rgn => Some(ObjVar(rgn), None)
       }
    }
  }
  
  def getPt(l : LocalPointerKey, localConstraints : MSet[LocalPtEdge], hg : HeapGraph[InstanceKey]) : Option[(ObjVar, Option[LocalPtEdge])] =
    getConstraintPt(l, localConstraints) match {
      //case Some((o, edge)) => (Some(o), Some(edge)) // found matching obj in local constraints
      case Some((o, edge)) => //(o, Some(edge)) // found matching obj in local constraints
        Some(o, Some(edge)) // found matching obj in local constraints
      case None => getPt(l, hg) match {
        case rgn if rgn.isEmpty => None
        case rgn => Some(ObjVar(rgn), None)
      }
        //(ObjVar(getPt(l, hg)), None) // l not in local constraints; need to look up in pts-to graph
    }
   
  def getPtVal(l : LocalPointerKey, localConstraints : MSet[LocalPtEdge], hg : HeapGraph[InstanceKey]) : (Val, Option[LocalPtEdge]) =
    localConstraints.find(edge => edge.src.key == l) match {
      case Some(edge) => (edge.snk, Some(edge))
      case None => getPt(l, hg) match {
        case set if !set.isEmpty => (ObjVar(set), None)
        case _ => (Pure.makePureVar(l), None) // create fresh pure var          
      }
    }
  
  def getPt(l : LocalPointerKey, fld : IField, localConstraints : MSet[LocalPtEdge], ptConstraints : MSet[HeapPtEdge],
            hg : HeapGraph[InstanceKey]) : ObjVar = {
    require(fld.getFieldTypeReference().isReferenceType())
    getConstraintPt(l, localConstraints) match {
      case Some((o, _)) => getPtO(o, fld, ptConstraints, hg)._1 // found matching obj in local constraints
      case None => ObjVar(getPtL(l, fld, hg)) // l not in local constraints; need to look up in pts-to graph
    }
  }            

  def getPtArr(arrRef : ObjVar, index : Option[PureVar], hg : HeapGraph[InstanceKey], hm : HeapModel,
               cha : IClassHierarchy) : ArrayPtEdge = {
    val arrKeys = arrRef.rgn.map(k => hm.getPointerKeyForArrayContents(k).asInstanceOf[ArrayContentsKey])

    assert(!arrKeys.isEmpty)
    val arrFld = Fld.makeArrayFld(arrKeys, index, cha)
    if (arrFld.isPrimitiveType) ArrayPtEdge(arrRef, arrFld, Pure.makePureVar(arrFld.arrayElementType))
    else {
      // TODO: check for primitive types
      val snkRgn = getSuccs[InstanceKey](arrKeys, hg)
      val snk = if (snkRgn.isEmpty) Pure.makePureVar(arrFld.typ.getArrayElementType()) else ObjVar(snkRgn)
      ArrayPtEdge(arrRef, arrFld, snk)
    }
  }
  
  // ==== consulting *only* constraints for points-to facts ====
  // getContraintPt methods only return points-to facts with heap RHS's (i.e., ObjVar's)
  // getConstraintVal methods return points-to facts with Val RHS's. A Val can be an ObjVar or a PureVal
  
  
  /** try to match @param lhs with the src of an edge in @param localConstraints 
   * if we find one, @return the edge and the RHS of the edge if it is an ObjVar, None if we do not find a matching edge
   * if the RHS of the edge is a PureVal, error
   */
  def getConstraintPt(lhs : LocalPointerKey, localConstraints : MSet[LocalPtEdge]) : Option[(ObjVar,LocalPtEdge)] = {
    localConstraints.find(edg => edg.src.key == lhs) match {
      case Some(edg) => edg.snk match {
        case o@ObjVar(_) => Some(o, edg) 
        case _ => sys.error("Bad snk for " + edg + "; expecting ObjVar; got " + edg.snk)
      }
      case None => None
    }
  }
  
  private def getLHSRegion(lhs : LocalPointerKey, localConstraints : MSet[LocalPtEdge], hg : HeapGraph[InstanceKey]) : Set[InstanceKey] =
    getConstraintPt(lhs, localConstraints) match {
      case Some((o@ObjVar(_), edge)) => o.rgn
      case None => getPt(lhs, hg)
    }  
  
  /** try to match the InstanceKeys pointed to by @param lhs with the instance keys of the src of an edge in @param heapConstraints */
  def getConstraintPt(lhs : LocalPointerKey, fld : IField, localConstraints : MSet[LocalPtEdge], 
                      heapConstraints : MSet[HeapPtEdge], hg : HeapGraph[InstanceKey]) : Option[Iterable[ObjPtEdge]] = {
    // get points-to region of lhs in the constraints or heap graph    
    val lhsRgn = getLHSRegion(lhs, localConstraints, hg)
    getConstraintPt(lhsRgn, fld, heapConstraints)
  }
  
  /** return ObjPtEdges with src @param obj and fld @param fld (i.e., edges of the form src.fld -> ... 
   *  call this only when the local constraints have an edge l -> obj. otherwise, call getConstraintPt(lhsRgn : Set[InstanceKey, ...) */
  def getConstraintPt(obj : ObjVar, fld : IField, heapConstraints : MSet[HeapPtEdge]) : Option[ObjPtEdge] = 
    heapConstraints.collectFirst({ case e@ObjPtEdge(o, f, _) if fld == f.fld && obj == o => e })

  /**
   * return ObjPtEdges with src @param obj and fld @param fld (i.e., edges of the form src.fld -> ... 
   * call this only when the local constraints do not have an edge l -> ObjVar(lhsRgn). otherwise, call getConstraintPt(obj : ObjVar, ...) */
  def getConstraintPt(lhsRgn : Set[InstanceKey], fld : IField, heapConstraints : MSet[HeapPtEdge]) : Option[Iterable[ObjPtEdge]] = 
    heapConstraints.collect({ case e@ObjPtEdge(ObjVar(rgn), f, _) 
      if fld == f.fld && !rgn.intersect(lhsRgn).isEmpty => e }) match {
        case edges if edges.isEmpty => None
        case edges => Some(edges)
    }

  /** try to match @param lhs with the src of an edge in @param localConstraints @return the matching edge if we find it, None otherwise */
  def getConstraintEdge(lhs : PointerKey, localConstraints : MSet[LocalPtEdge]) : Option[LocalPtEdge] =
    localConstraints.find(edg => edg.src.key == lhs)

  // ==== ptBy -- get predecessors in points-to graph ====
  def getPtByFld(rgn : Set[InstanceKey], fld : IField, hg : HeapGraph[InstanceKey]) : Set[InstanceKey] =
    getPtBy(rgn, key => key match {
      case key : InstanceFieldKey if key.getField() == fld => Some(key.getInstanceKey())
      case _ => None
    }, hg)
    
  def getPtByArr(rgn : Set[InstanceKey], hg : HeapGraph[InstanceKey]) : Set[InstanceKey] =
    getPtBy(rgn, key => key match {
      case key : ArrayContentsKey => Some(key.getInstanceKey())
      case _ => None
    }, hg)
    
  def getPtBy(rgn : Set[InstanceKey], predOk : Object => Option[InstanceKey],
              hg : HeapGraph[InstanceKey]) : Set[InstanceKey] =
    rgn.foldLeft (Set.empty[InstanceKey]) ((keys, key) =>
      hg.getPredNodes(key).foldLeft (keys) ((keys, key) =>
        predOk(key) match {
          case Some(k) => keys + k
          case None => keys
        }
      )
    )
    
  // TODO: eliminate this
  // ==== old PTUtil ====
  def instanceKeyOrErr : PartialFunction[Any,InstanceKey] = { 
    case k : InstanceKey => k 
    case k => sys.error("Expecting instance key; found " + k)
  }
  
  def get(base : Object, hg : HeapGraph[InstanceKey]) : Set[InstanceKey] =
    hg.getSuccNodes(base).collect({ case i : InstanceKey => i}).toSet
    
  def contains(base : Object, toFind : Set[InstanceKey], hg : HeapGraph[InstanceKey]) : Boolean =
    hg.getSuccNodes(base).exists(node => toFind.contains(node.asInstanceOf[InstanceKey])) 
    
  def contains(base : Object, fld : IField, toFind : Set[InstanceKey],
               hg : HeapGraph[InstanceKey]) : Boolean = base match {
    case l : LocalPointerKey => 
      hg.getSuccNodes(l).exists(instanceKey => contains(instanceKey, fld, toFind, hg))      
    case i : InstanceKey =>
      hg.getSuccNodes(i).exists({ 
        case f : InstanceFieldKey => f.getField() == fld && 
          hg.getSuccNodes(f).exists(key => toFind.contains(key)) 
        case other => sys.error("unexpected kind of key " + other) })
    case other => sys.error("bad base : " + other + " type " + other.getClass())
  }
  
  // TODO: this is pretty terrible...
  def arrContains(base : Object, toFind : Set[InstanceKey], hg : HeapGraph[InstanceKey]) : Boolean = base match {
    case l : LocalPointerKey => 
      hg.getSuccNodes(l).exists(instanceKey => arrContains(instanceKey, toFind, hg))      
    case i : InstanceKey => hg.getSuccNodes(i).exists(
      { case k : ArrayContentsKey => 
        hg.getSuccNodes(k).exists(key => toFind.contains(key.asInstanceOf[InstanceKey])) })
    case other => sys.error("bad base : " + other + " type " + other.getClass())
  }
  
  def contains(base : Object, toFind : InstanceKey, hg : HeapGraph[InstanceKey]) : Boolean =
    hg.getSuccNodes(base).exists(node => node == toFind)
  
  def contains(base : Object, fld : IField, toFind : InstanceKey, hg : HeapGraph[InstanceKey]) : Boolean = base match {
    case l : LocalPointerKey => 
      hg.getSuccNodes(l).exists(instanceKey => contains(instanceKey, fld, toFind, hg))      
    case i : InstanceKey => hg.getSuccNodes(i).exists(
      { case f : InstanceFieldKey if f.getField() == fld => 
        hg.getSuccNodes(f).exists(key => key == toFind) })
    case other => sys.error("bad base : " + other + " type " + other.getClass())
  }

  def getLocalPreds(keys : Set[InstanceKey], hg : HeapGraph[InstanceKey]) : Set[LocalPointerKey] =
    keys.foldLeft (Set.empty[LocalPointerKey]) ((s, key) => hg.getPredNodes(key).foldLeft (s) ((s, k) => k match {
      case k : LocalPointerKey => s + k
      case _ => s
    }))

}