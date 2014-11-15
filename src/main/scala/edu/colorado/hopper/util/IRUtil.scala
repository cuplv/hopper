package edu.colorado.hopper.util

import scala.collection.JavaConversions._
import com.ibm.wala.types.FieldReference
import com.ibm.wala.ssa.SSAPutInstruction
import com.ibm.wala.ssa.IR
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ssa.SSAArrayStoreInstruction
import com.ibm.wala.ssa.SSAInstruction
import com.ibm.wala.ssa.SymbolTable
import com.ibm.wala.classLoader.IField
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey
import com.ibm.wala.classLoader.JavaLanguage
import com.ibm.wala.types.TypeReference
import com.ibm.wala.classLoader.IMethod
import com.ibm.wala.ipa.callgraph.AnalysisCache
import com.ibm.wala.ipa.callgraph.impl.Everywhere
import com.ibm.wala.ssa.SSAOptions
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.types.MethodReference
import com.ibm.wala.classLoader.IBytecodeMethod

object IRUtil {

  val factory = new JavaLanguage.JavaInstructionFactory

  var dummyIndexCounter = 0
  def getDummyIndex() : Int = {
    dummyIndexCounter += 1
    dummyIndexCounter
  }

  def makeIR(m : MethodReference, cha : IClassHierarchy) : IR = makeIR(cha.resolveMethod(m), None)
  
  // utility for creating IR for a method without constructing a call graph
  def makeIR(m : IMethod, analysisCache : Option[AnalysisCache] = None) : IR = {
    val cache = analysisCache match {
      case Some(analysisCache) => analysisCache
      case None => new AnalysisCache
    }
    cache.getSSACache().findOrCreateIR(m, Everywhere.EVERYWHERE, SSAOptions.defaultOptions()) 
  }
    
  /** get all instructions for @param node and generate assignments of instance/static fields to default values, if appropriate 
   *  this second step is important because WALA does not generate code for these (implicit) instructions and we sometimes need
   *  these assignments to produce/refute some constraint 
   *  
  **/
  //  TODO: this code isn't completely right because it depends on WALA to generate constructor and class initializer CGNode's for
  // all classes, which it sometimes does not do if the class initializer or constructor has no code.
  //  If WALA does not generate a class initializer for some class C and C has a static
  //  field f, then we will never generate a C.f = null assignment, which could lead to a failure to find producers in some cases 
  // TODO : cache?
  def getAllInstructions(node : CGNode) : List[SSAInstruction] = {
    val ir = node.getIR()
    if (ir == null) List.empty[SSAInstruction]
    else {
      val method = node.getMethod()
      val regInstrs = ir.iterateAllInstructions().toList
      if (method.isInit()) addDefaultValueAssignmentsForInstanceFields(regInstrs, ir)
      else if (method.isClinit()) addDefaultValueAssignmentsForStaticFields(regInstrs, ir)
      else regInstrs
    }
  }
 
  // TODO: should just move this elsewhere and make my own wrapper for the WALA IR that is the only IR the symbolic executor, relevance graph, e.t.c ever see
 /**
   * Explicitly generate assignments of non-final fields to default values and place them at the beginning
   * of constructors (for instance fields) or class initializers (for static fields). In WALA IR, these assignments are implicit.
   */
  def addDefaultValueAssignmentsForInstanceFields(instrs : List[SSAInstruction], ir : IR) = {
    require(ir.getMethod().isInit())
    val tbl = ir.getSymbolTable()
    val thisVar = 1
    def mkInstr (valu : Int, ref : FieldReference) : SSAPutInstruction =
      factory.PutInstruction(getDummyIndex(), thisVar, valu, ref)
    ir.getMethod().getDeclaringClass().getDeclaredInstanceFields().foldLeft (instrs) ((instrs, fld) =>
      getDefaultAssignment(fld, tbl, mkInstr) :: instrs)
  }
  
  def addDefaultValueAssignmentsForStaticFields(instrs : List[SSAInstruction], ir : IR) = {
    require(ir.getMethod().isClinit())
    val tbl = ir.getSymbolTable()
    def mkInstr (valu : Int, ref : FieldReference) : SSAPutInstruction =
      factory.PutInstruction(getDummyIndex(), valu, ref)
    ir.getMethod().getDeclaringClass().getAllStaticFields().foldLeft (instrs) ((instrs, fld) =>
      getDefaultAssignment(fld, tbl, mkInstr) :: instrs)
  }
  
  // generate default value assignment for a *particular* field. needed in the deviant case where WALA generates no class initializer for a class
  def getDefaultValueAssignmentForStaticField(f : StaticFieldKey) : SSAPutInstruction = 
    factory.PutInstruction(getDummyIndex(), 0, f.getField().getReference())

  // given an array write, generate a write to the same array, same index, but writing the default value 0
  def getDefaultValueAssigmentForArrayIndex(i : SSAArrayStoreInstruction) : SSAArrayStoreInstruction = 
    factory.ArrayStoreInstruction(getDummyIndex(), i.getArrayRef(), i.getIndex(), 0, i.getElementType())
   
  def getDefaultAssignment(fld : IField, tbl : SymbolTable, mkInstr : (Int, FieldReference) => SSAPutInstruction) : SSAPutInstruction = {
    // TODO: something smarter here?
    val default = fld.getFieldTypeReference() match {
      case TypeReference.Int => tbl.getConstant(0)
      case TypeReference.Boolean => tbl.getConstant(false)
      case TypeReference.Float => tbl.getConstant(0f)
      case TypeReference.Long => tbl.getConstant(0l)
      case TypeReference.Double => tbl.getConstant(0.0)
      case TypeReference.Char => tbl.getConstant('\u0000') 
      case TypeReference.Byte => tbl.getConstant(0.toByte) 
      case TypeReference.Short => tbl.getConstant(0.toShort)
      case t if t.isReferenceType() => tbl.getNullConstant() 
      case t => Util.unimp("Getting default assignment for unknown type " + t)
    }
    mkInstr(default, fld.getReference())
  }
  
  def getSourceLine(bcIndex : Int, m : IBytecodeMethod) : Int = m.getLineNumber(bcIndex)  
  
  def getSourceLine(i : SSAInstruction, ir : IR) : Int = ir.getMethod() match {
    case m : IBytecodeMethod => 
      val instrIndex = ir.getInstructions().indexOf(i)
      if (instrIndex >= 0) {
        val bcIndex = m.getBytecodeIndex(instrIndex)
        getSourceLine(bcIndex, m)
      } else -1
    case _ => -1
  }
  
}  