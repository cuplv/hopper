package edu.colorado.hopper.state

import com.ibm.wala.analysis.reflection.InstanceKeyWithNode
import com.ibm.wala.analysis.typeInference.TypeInference
import com.ibm.wala.classLoader.IClass
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.callgraph.propagation.{HeapModel, InstanceKey, LocalPointerKey, PointerKey, ReturnValueKey}
import com.ibm.wala.shrikeBT.{IBinaryOpInstruction, IConditionalBranchInstruction, IShiftInstruction, IUnaryOpInstruction}
import com.ibm.wala.ssa.{SSAConditionalBranchInstruction, SymbolTable}
import com.ibm.wala.types.TypeReference
import edu.colorado.hopper.util.Types._
import edu.colorado.hopper.util.{ClassUtil, Util}

/**
 * Base components of analysis state--Val's and Var's
 */
sealed trait Val {
  def isArrayType : Boolean
  def |=(v : Val) : Boolean
}
sealed trait Var

trait PureConstraint {  
  def isStringConstraint : Boolean 
  def isBitwiseConstraint : Boolean
  def isFloatConstraint : Boolean
  def isLongConstraint : Boolean
  def getVars(s : Set[PureVar] = Set.empty) : Set[PureVar]
}

case class PureAtomicConstraint(val lhs : PureExpr, val op : CmpOp, val rhs : PureExpr) extends PureConstraint {  
  def isEqualityConstraint : Boolean = Pure.isEqualityOp(op)
  def isInequalityConstraint : Boolean = Pure.isInequalityOp(op)
  override def isStringConstraint : Boolean = lhs.isStringExpr || rhs.isStringExpr
  override def isBitwiseConstraint : Boolean = lhs.isBitwiseExpr || rhs.isBitwiseExpr
  override def isFloatConstraint : Boolean = lhs.isFloatExpr || rhs.isFloatExpr
  override def isLongConstraint : Boolean = lhs.isLongExpr || rhs.isLongExpr
  override def getVars(s : Set[PureVar]) : Set[PureVar] = lhs.getVars(rhs.getVars(s))
  
  override def clone : PureConstraint = this
  override def hashCode : Int = Util.makeHash(List(lhs, op, rhs))
  override def equals(other : Any) : Boolean = other match {
    case p : PureAtomicConstraint => this.lhs == p.lhs && this.op == p.op && this.rhs == p.rhs
    case _ => false
  }
  override def toString : String = lhs.toString + " " + Pure.cmpOpToString(op) + " " + rhs.toString()
}

case class PureDisjunctiveConstraint(val terms : Set[PureAtomicConstraint]) extends PureConstraint {
  require(!terms.isEmpty)
  override def isStringConstraint : Boolean = terms.exists(p => p.isStringConstraint)
  override def isBitwiseConstraint : Boolean = terms.exists(p => p.isBitwiseConstraint)
  override def isFloatConstraint : Boolean = terms.exists(p => p.isFloatConstraint)
  override def isLongConstraint : Boolean = terms.exists(p => p.isLongConstraint)
  override def getVars(s : Set[PureVar]) : Set[PureVar] = terms.foldLeft (Set.empty[PureVar]) ((s, t) => t.getVars(s))
  
  override def clone : PureConstraint = this
  override def hashCode : Int = Util.makeHash(terms.toList)
  override def equals(other : Any) : Boolean = other match {
    case p : PureDisjunctiveConstraint => this.terms == terms
    case _ => false
  }
  override def toString : String = Util.toCSVStr(terms, " V ")
}

abstract class PureExpr {
  def substitute(toSub : PureExpr, subFor : PureVar) : PureExpr
  def isStringExpr : Boolean = false
  def isBitwiseExpr : Boolean = false
  def isFloatExpr : Boolean = false
  def isLongExpr : Boolean = false
  def getVars(s : Set[PureVar] = Set.empty) : Set[PureVar]
  
  override def clone : PureExpr = this
}

// constant values
abstract class PureVal(val v : Any) extends PureExpr {
  override def substitute(toSub : PureExpr, subFor : PureVar) : PureVal = this     
  
  def >(p : PureVal) : Boolean = sys.error("GT for arbitrary PureVal")
  def <(p : PureVal) : Boolean = sys.error("LT for arbitrary PureVal")
  def >=(p : PureVal) : Boolean = sys.error("GE for arbitrary PureVal")
  def <=(p : PureVal) : Boolean = sys.error("LE for arbitrary PureVal")
  override def isStringExpr : Boolean = this.isInstanceOf[StringVal]
  override def getVars(s : Set[PureVar] = Set.empty) : Set[PureVar] = s
  
  override def hashCode : Int = Util.makeHash(List(v))
  override def equals(other : Any) : Boolean = other match {
    case p : PureVal => this.v == p.v
    case _ => false
  }  
  override def toString : String = v.toString
}

case class BoolVal(override val v : Boolean) extends PureVal(v)
case class IntVal(override val v : Int) extends PureVal(v) {
  override def >(p : PureVal) : Boolean = v > p.asInstanceOf[IntVal].v 
  override def <(p : PureVal) : Boolean = v < p.asInstanceOf[IntVal].v 
  override def >=(p : PureVal) : Boolean = v >= p.asInstanceOf[IntVal].v 
  override def <=(p : PureVal) : Boolean = v <= p.asInstanceOf[IntVal].v 
}
case class DoubleVal(override val v : Double) extends PureVal(v) {
  override def >(p : PureVal) : Boolean = v > p.asInstanceOf[DoubleVal].v 
  override def <(p : PureVal) : Boolean = v < p.asInstanceOf[DoubleVal].v 
  override def >=(p : PureVal) : Boolean = v >= p.asInstanceOf[DoubleVal].v 
  override def <=(p : PureVal) : Boolean = v <= p.asInstanceOf[DoubleVal].v 
}
case class FloatVal(override val v : Float) extends PureVal(v) {
  override def isFloatExpr : Boolean = true
  override def >(p : PureVal) : Boolean = v > p.asInstanceOf[FloatVal].v 
  override def <(p : PureVal) : Boolean = v < p.asInstanceOf[FloatVal].v 
  override def >=(p : PureVal) : Boolean = v >= p.asInstanceOf[FloatVal].v 
  override def <=(p : PureVal) : Boolean = v <= p.asInstanceOf[FloatVal].v 
}
case class LongVal(override val v : Long) extends PureVal(v) {
  override def isLongExpr : Boolean = true
  override def >(p : PureVal) : Boolean = v > p.asInstanceOf[LongVal].v 
  override def <(p : PureVal) : Boolean = v < p.asInstanceOf[LongVal].v 
  override def >=(p : PureVal) : Boolean = v >= p.asInstanceOf[LongVal].v 
  override def <=(p : PureVal) : Boolean = v <= p.asInstanceOf[LongVal].v 
}
case class CharVal(override val v : Char) extends PureVal(v) {
  override def >(p : PureVal) : Boolean = v > p.asInstanceOf[CharVal].v 
  override def <(p : PureVal) : Boolean = v < p.asInstanceOf[CharVal].v 
  override def >=(p : PureVal) : Boolean = v >= p.asInstanceOf[CharVal].v 
  override def <=(p : PureVal) : Boolean = v <= p.asInstanceOf[CharVal].v 
}
case class StringVal(override val v : String) extends PureVal(v)   

case class PureVar(val typ : TypeReference) extends PureExpr with Val {
  val id : Int = Var.getFreshPureVarId
  
  override def isArrayType : Boolean = false
  override def isStringExpr : Boolean = typ == TypeReference.JavaLangString
  override def isFloatExpr : Boolean = typ == TypeReference.Float
  override def isLongExpr : Boolean = typ == TypeReference.Long
  def isReferenceType : Boolean = typ.isReferenceType()
  
  // TODO: should we ask Z3 here? may be sound to do something coarser if we are careful about our usage of this
  override def |=(other : Val) : Boolean = other match {
    case PureVar(oType) => typ == oType // this == other
    case _ => false
  }
  override def getVars(s : Set[PureVar]) : Set[PureVar] = s + this

  override def substitute(toSub : PureExpr, subFor : PureVar) : PureExpr = if (subFor == this) toSub else this
  
  override def hashCode : Int = Util.makeHash(List(id))
  override def equals(other : Any) : Boolean = other match {
    case p : PureVar => this.id == p.id
    case _ => false
  }
  override def toString : String = "p-" + id
}

case class PureBinExpr(lhs : PureExpr, op : BinOp, rhs : PureExpr) extends PureExpr {
  override def substitute(toSub : PureExpr, subFor : PureVar) : PureBinExpr = 
    PureBinExpr(lhs.substitute(toSub, subFor), op, rhs.substitute(toSub, subFor))
  override def getVars(s : Set[PureVar]) : Set[PureVar] = lhs.getVars(rhs.getVars(s))

  override def isStringExpr : Boolean = lhs.isStringExpr || rhs.isStringExpr
  override def isBitwiseExpr : Boolean = op match {
    case IBinaryOpInstruction.Operator.OR => true
    case IBinaryOpInstruction.Operator.AND => true
    case IBinaryOpInstruction.Operator.XOR => true
    case IShiftInstruction.Operator.SHL => true
    case IShiftInstruction.Operator.SHR => true
    case IShiftInstruction.Operator.USHR => true
    case _ => false
  }
  override def hashCode : Int = Util.makeHash(List(lhs, op, rhs))
  override def equals(other : Any) : Boolean = other match {
    case p : PureBinExpr => this.lhs == p.lhs && this.op == p.op && this.rhs == p.rhs
    case _ => false
  }
  override def toString : String = lhs.toString + " " + Pure.binOpToString(op) + " " + rhs.toString
}

abstract class StackVar(val key : PointerKey) extends Var {
  def getNode : CGNode
  override def hashCode : Int = key.hashCode()
  override def equals(other : Any) : Boolean = other match {
    case s : StackVar => this.key == s.key
    case _ => false
  }
}
case class LocalVar(override val key : LocalPointerKey) extends StackVar(key) {
  def isParam : Boolean = key.isParameter  
  override def getNode : CGNode = key.getNode()
  override def toString : String = key.getNode().getMethod.getName.toString + "-v" + key.getValueNumber()
  //override def toString : String = ClassUtil.pretty(key.getNode()) + "-v" + key.getValueNumber()
}
case class ReturnVar(override val key : ReturnValueKey) extends StackVar(key) {
  override def getNode : CGNode = key.getNode()
  override def toString : String = ClassUtil.pretty(key.getNode()) + "-ret"
}

abstract class HeapVar extends Var {
  def isClinitVar : Boolean
}

case class ClassVar(cls : IClass) extends HeapVar {
  override def isClinitVar : Boolean = true
  override def hashCode : Int = cls.hashCode()
  override def equals(other : Any) : Boolean = other match {
    case ClassVar(c) => this.cls == c
    case _ => false
  }
  override def toString : String = ClassUtil.pretty(cls)
}

case class ObjVar(rgn : Set[InstanceKey]) extends HeapVar with Val {  
  require(!rgn.isEmpty, "Can't create ObjVar from empty region!")
  
  val cantAlias : MSet[Int] = Util.makeSet
  
  val id = Var.getFreshObjId    
  
  override def isClinitVar : Boolean = rgn.forall(k => k match {
    case k : InstanceKeyWithNode => k.getNode().getMethod().isClinit()
    case _ => false // not sure, assume false
  })
  
  override def isArrayType : Boolean = rgn.exists(key => key.getConcreteType().isArrayClass())
  
  override def |=(other : Val) : Boolean = other match {
    case o@ObjVar(oRgn) => rgn.subsetOf(oRgn)
    case _ => false
  }
  
  override def hashCode : Int = id * Util.PRIME
  override def equals(other : Any) : Boolean = other match {
    case o@ObjVar(_) => this.id == o.id
    case _ => false
  }
  override def toString : String = if (rgn.size == 1) id + "-" + ClassUtil.pretty(rgn.head)
    else s"$id-${ClassUtil.pretty(rgn.head.getConcreteType())}(${rgn.size})"
  //override def toString : String =  
    //id + "-" + ClassUtil.pretty(rgn.head.getConcreteType()) + "<RGN>\n" + rgn.foldLeft ("") ((str, ele>) => str + "\n" + elem) + "<eRGN>\n"
}

object Var {
  private var objIdCounter = 0
  def getFreshObjId : Int = { objIdCounter += 1; objIdCounter }
  private var pureVarIdCounter = 0
  def getFreshPureVarId : Int = { pureVarIdCounter += 1; pureVarIdCounter }
  
  def makeLPK(valueNum : Int, n : CGNode, hm : HeapModel) : LocalPointerKey =
    hm.getPointerKeyForLocal(n, valueNum).asInstanceOf[LocalPointerKey]
 
  def makeRVK(n : CGNode, hm : HeapModel) : ReturnValueKey = 
    hm.getPointerKeyForReturnValue(n).asInstanceOf[ReturnValueKey]
  
  def makeReturnVar(n : CGNode, hm : HeapModel) : ReturnVar = ReturnVar(makeRVK(n, hm))
  
  def makeLocalVar(valueNum : Int, n : CGNode, hm : HeapModel) : LocalVar = LocalVar(makeLPK(valueNum, n, hm))    
  
  def makeThisVar(n : CGNode, hm : HeapModel) : LocalVar = makeLocalVar(1, n, hm)
  
  def markCantAlias(o1 : ObjVar, o2 : ObjVar) : Unit = {
    o1.cantAlias.add(o2.id)
    o2.cantAlias.add(o1.id)
  }
  
  def canAlias(o1 : ObjVar, o2 : ObjVar) : Boolean = !o1.cantAlias.contains(o2.id) && !o2.cantAlias.contains(o1.id)
}

object Pure {  
  
  val NULL = BoolVal(false)
  val NON_NULL = BoolVal(true)
  
  def evaluateConstConditional(tbl : SymbolTable, i : SSAConditionalBranchInstruction) : Boolean = {
    require(tbl.isConstant(i.getUse(0)) && tbl.isConstant(i.getUse(1)))
    val (lhs, rhs) = (makePureVal(tbl, i.getUse(0)), makePureVal(tbl, i.getUse(1)))
    i.getOperator() match {
      case IConditionalBranchInstruction.Operator.EQ => lhs.v == rhs.v
      case IConditionalBranchInstruction.Operator.NE => lhs.v != rhs.v
      case IConditionalBranchInstruction.Operator.GT => lhs > rhs
      case IConditionalBranchInstruction.Operator.LT => lhs < rhs
      case IConditionalBranchInstruction.Operator.GE => lhs >= rhs
      case IConditionalBranchInstruction.Operator.LE => lhs <= rhs
    }    
  } 
  
  /** @param l - LocalPointerKey that will point at the pure var*/
  def makePureVar(l : LocalPointerKey) : PureVar = {
    val (ir, valNum) = (l.getNode.getIR, l.getValueNumber()) 
    //require(!ir.getSymbolTable().isConstant(valNum))

    // infer type for all local vars, including primitives    
    val typeInference = TypeInference.make(ir, true)
    val typeRef = typeInference.getType(valNum).getTypeReference
    if (typeRef == null) makePureIntVar // this happens with the special WALA TOP type. assume int    
    else makePureVar(typeRef)
  }  
  
  // convert bitshifting by a constant to multiplication/division when possible
  def makePureBinExpr(lhs : PureExpr, op : BinOp, rhs : PureExpr) : PureExpr = (op, rhs) match {
    case (IShiftInstruction.Operator.SHL, IntVal(n)) =>
      def mult2(expr : PureExpr, n : Int) : PureExpr = n match {
        case 0 => expr
        case n => mult2(PureBinExpr(expr, IBinaryOpInstruction.Operator.MUL, IntVal(2)), n - 1)
      }      
      mult2(lhs, n)
    case (IShiftInstruction.Operator.SHR, IntVal(n)) =>
      def div2(expr : PureExpr, n : Int) : PureExpr = n match {
        case 0 => expr
        case n => div2(PureBinExpr(expr, IBinaryOpInstruction.Operator.DIV, IntVal(2)), n - 1)
      }
      div2(lhs, n)
    case _ => PureBinExpr(lhs, op, rhs)
  }
  
  def makePureIntVar : PureVar = PureVar(TypeReference.Int)
  def makePureBoolVar : PureVar = PureVar(TypeReference.Boolean)
  def makePureObjVar : PureVar = PureVar(TypeReference.JavaLangObject) 
  
  def makePureVar(typ : TypeReference) : PureVar = {
    //require(typ.isPrimitiveType(), "expected primitive type, got " + typ) // TODO: not sure if it's ok to do null consts here    
    // TODO: we convert everything to ints for convenience -- support bools for better Z3 performance
    if (!typ.isPrimitiveType()) makePureObjVar // this should only be called if we're creating a value to compare to null
    else if (typ == TypeReference.Boolean) makePureIntVar
    else PureVar(typ)
  }
  
  def makePureVal(tbl : SymbolTable, useNum : Int) : PureVal = {
    require(tbl.isConstant(useNum))
    
    if (tbl.isIntegerConstant(useNum)) IntVal(tbl.getIntValue(useNum))
    //else if (tbl.isBooleanConstant(useNum)) BoolVal(tbl.isTrue(useNum))
    else if (tbl.isBooleanConstant(useNum)) if (tbl.isTrue(useNum)) IntVal(1) else IntVal(0)
    else if (tbl.isNullConstant(useNum)) BoolVal(false)
    else if (tbl.isDoubleConstant(useNum)) DoubleVal(tbl.getDoubleValue(useNum))
    else if (tbl.isFloatConstant(useNum)) FloatVal(tbl.getFloatValue(useNum))
    else if (tbl.isLongConstant(useNum)) LongVal(tbl.getLongValue(useNum))
    else if (tbl.isStringConstant(useNum)) StringVal(tbl.getStringValue(useNum)) 
    else sys.error("Unknown constant type for use " + useNum)
  }  
  
  def makePureDisjunctiveConstraint(terms : Set[PureAtomicConstraint]) : PureConstraint = 
    if (terms.size == 1) terms.head
    else PureDisjunctiveConstraint(terms)
  
  def makeEqConstraint(op1 : PureExpr, op2 : PureExpr) : PureAtomicConstraint = 
    new PureAtomicConstraint(op1, IConditionalBranchInstruction.Operator.EQ, op2)
  def makeNeConstraint(op1 : PureExpr, op2 : PureExpr) : PureAtomicConstraint = 
    new PureAtomicConstraint(op1, IConditionalBranchInstruction.Operator.NE, op2)
  def makeEqBoolConstraint(op : PureExpr, b : Boolean) : PureAtomicConstraint = makeEqConstraint(op, IntVal(if (b) 1 else 0))
  def makeEqNullConstraint(op : PureVar) : PureAtomicConstraint = makeEqConstraint(op, Pure.NULL)
  def makeNeNullConstraint(op : PureVar) : PureAtomicConstraint = makeNeConstraint(op, Pure.NULL)
  def makeGtConstraint(op1 : PureExpr, op2 : PureExpr) : PureAtomicConstraint =
    new PureAtomicConstraint(op1, IConditionalBranchInstruction.Operator.GT, op2)  
  def makeGeConstraint(op1 : PureExpr, op2 : PureExpr) : PureAtomicConstraint =
    new PureAtomicConstraint(op1, IConditionalBranchInstruction.Operator.GE, op2)  
  def makeLtConstraint(op1 : PureExpr, op2 : PureExpr) : PureAtomicConstraint =
    new PureAtomicConstraint(op1, IConditionalBranchInstruction.Operator.LT, op2)  
  def makeLeConstraint(op1 : PureExpr, op2 : PureExpr) : PureAtomicConstraint =
    new PureAtomicConstraint(op1, IConditionalBranchInstruction.Operator.LE, op2)
   
  def makeDefaultVal(typ : TypeReference) : PureVal = typ match {
    case TypeReference.Int => IntVal(0)
    case TypeReference.Char => IntVal(0) // we model chars, bytes, and shorts as ints for now 
    case TypeReference.Byte => IntVal(0)
    case TypeReference.Short => IntVal(0)
    case TypeReference.Boolean => BoolVal(false)
    case TypeReference.Double => DoubleVal(0.0)
    case TypeReference.Float => FloatVal(0f)
    case TypeReference.Long => LongVal(0l)
    case TypeReference.JavaLangObject => BoolVal(false)
    case _ => sys.error("Unsupported type " + typ)
  }
  
  def makeDefaultValConstraint(op1 : PureVar) : PureConstraint = makeEqConstraint(op1, makeDefaultVal(op1.typ))
  
  def isInequalityOp(op : CmpOp) : Boolean = op == IConditionalBranchInstruction.Operator.NE  
  def isEqualityOp(op : CmpOp) : Boolean = op == IConditionalBranchInstruction.Operator.EQ
  
  def isNegateOp(op : UnOp) : Boolean = op == IUnaryOpInstruction.Operator.NEG 
  
  def negateCmpOp(op : CmpOp) : CmpOp = op match {
    case IConditionalBranchInstruction.Operator.EQ => IConditionalBranchInstruction.Operator.NE
    case IConditionalBranchInstruction.Operator.NE => IConditionalBranchInstruction.Operator.EQ
    case IConditionalBranchInstruction.Operator.GT => IConditionalBranchInstruction.Operator.LE
    case IConditionalBranchInstruction.Operator.LT => IConditionalBranchInstruction.Operator.GE
    case IConditionalBranchInstruction.Operator.GE => IConditionalBranchInstruction.Operator.LT
    case IConditionalBranchInstruction.Operator.LE => IConditionalBranchInstruction.Operator.GT
    case _ => sys.error("Unrecognized comparison operator " + op)
  }
  
  def cmpOpToString(op : CmpOp) : String = op match {
    case IConditionalBranchInstruction.Operator.EQ => "=="
    case IConditionalBranchInstruction.Operator.NE => "!="
    case IConditionalBranchInstruction.Operator.GT => ">"
    case IConditionalBranchInstruction.Operator.LT => "<"
    case IConditionalBranchInstruction.Operator.GE => ">="
    case IConditionalBranchInstruction.Operator.LE => "<="
    case _ => sys.error("Unrecognized comparison operator " + op)  
  }
  
  def binOpToString(op : BinOp) : String = op match {
    case IBinaryOpInstruction.Operator.ADD => "+"
    case IBinaryOpInstruction.Operator.SUB => "-"
    case IBinaryOpInstruction.Operator.MUL => "*"
    case IBinaryOpInstruction.Operator.DIV => "/"
    case IBinaryOpInstruction.Operator.REM => "%"
    case IBinaryOpInstruction.Operator.AND => "&"
    case IBinaryOpInstruction.Operator.OR => "|"
    case IBinaryOpInstruction.Operator.XOR => "^"
    case IShiftInstruction.Operator.SHL => "<<"
    case IShiftInstruction.Operator.SHR => ">>"
    case IShiftInstruction.Operator.USHR => ">>>"
    case _ => sys.error("Unrecognized binary operator " + op)    
  }
}
