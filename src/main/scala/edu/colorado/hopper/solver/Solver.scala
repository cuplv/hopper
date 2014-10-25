package edu.colorado.hopper.solver

import com.ibm.wala.shrikeBT.{IBinaryOpInstruction, IConditionalBranchInstruction}
import com.ibm.wala.types.TypeReference
import edu.colorado.hopper.state.{BoolVal, CharVal, IntVal, PureAtomicConstraint, PureBinExpr, PureConstraint, PureDisjunctiveConstraint, PureExpr, PureVar}
import edu.colorado.hopper.util.Types._

trait Assumptions

class UnknownSMTResult(msg : String) extends Exception(msg)

/** SMT solver parameterized by its AST or expression type */
trait Solver[T] {
  // checking
  def checkSAT : Boolean
  def checkSATWithAssumptions(assumes : List[String]) : Boolean
  def checkTemporaryConstraint(a : PureConstraint, assumes : List[String]) : Boolean = {
    push
    mkAssert(toAST(a))
    val res = checkSATWithAssumptions(assumes)
    pop
    res
  }

  def getUNSATCore : String
  def push() : Unit
  def pop() : Unit
  
  // cleanup
  def dispose() : Unit
  // conversion from pure constraints to AST type of solver (T)
  def mkAssert(p : PureConstraint) : Unit = mkAssert(toAST(p))
  def mkAssertWithAssumption(assume : String, p : PureConstraint) : Unit = mkAssert(mkImplies(mkBoolVar(assume), toAST(p)))    
  
  // comparison operations
  protected def mkEq(lhs : T, rhs : T) : T
  protected def mkNe(lhs : T, rhs : T) : T
  protected def mkGt(lhs : T, rhs : T) : T
  protected def mkLt(lhs : T, rhs : T) : T
  protected def mkGe(lhs : T, rhs : T) : T
  protected def mkLe(lhs : T, rhs : T) : T
  
  // logical and arithmetic operations
  protected def mkNot(o : T) : T
  protected def mkImplies(lhs : T, rhs : T) : T
  
  protected def mkAdd(lhs : T, rhs : T) : T
  protected def mkSub(lhs : T, rhs : T) : T
  protected def mkMul(lhs : T, rhs : T) : T
  protected def mkDiv(lhs : T, rhs : T) : T
  protected def mkRem(lhs : T, rhs : T) : T
  protected def mkAnd(lhs : T, rhs : T) : T 
  protected def mkOr(lhs : T, rhs : T) : T 
  protected def mkXor(lhs : T, rhs : T) : T  
  
  // creation of variables, constants, assertions
  protected def mkIntVal(i : Int) : T
  protected def mkBoolVal(b : Boolean) : T
  protected def mkIntVar(s : String) : T    
  protected def mkBoolVar(s : String) : T
  protected def mkAssert(t : T) : Unit
  
  def toAST(p : PureConstraint) : T = p match {
    case PureAtomicConstraint(lhs, op, rhs) => toAST(toAST(lhs), op, toAST(rhs))
    case PureDisjunctiveConstraint(terms) => terms.foldLeft (None : Option[T]) ((combined, term) => combined match {
      case Some(combined) => Some(mkOr(toAST(term), combined))
      case None => Some(toAST(term))
    }).get
  }
  
  /**
   * Maps a variable to a name that will represent it in the solver.
   */
  protected def getSolverName(p : PureVar): String = p match {
    case PureVar(typ) =>
      val id = p.id
      typ match {
        case TypeReference.Int => "i" + id.toString
        case TypeReference.Byte => "i" + id.toString // we treat bytes, shorts, chars as ints for now
        case TypeReference.Short => "i" + id.toString
        case TypeReference.Char => "i" + id.toString
        case TypeReference.Boolean => "b" + id.toString // TODO: should we allow bools? or convert them all to ints?
        case TypeReference.JavaLangObject => "o" + id.toString // objects are bools where false means null and true means non-null
        case _ => sys.error("Bad type for pure var " + p + ": type " + typ + " expecting " + TypeReference.Int)
      }
  }
  
  // conversion from pure expressions to AST type of solver (T)
  protected def toAST(p : PureExpr) : T = p match {
    case PureBinExpr(lhs, op, rhs) =>
      val (_lhs, _rhs) = (toAST(lhs), toAST(rhs))
      op match {
        case IBinaryOpInstruction.Operator.ADD => mkAdd(_lhs, _rhs)
        case IBinaryOpInstruction.Operator.SUB => mkSub(_lhs, _rhs)
        case IBinaryOpInstruction.Operator.MUL => mkMul(_lhs, _rhs)
        case IBinaryOpInstruction.Operator.DIV => mkDiv(_lhs, _rhs)
        case IBinaryOpInstruction.Operator.REM => mkRem(_lhs, _rhs)
        case IBinaryOpInstruction.Operator.AND => mkAnd(_lhs, _rhs)
        case IBinaryOpInstruction.Operator.OR => mkOr(_lhs, _rhs)
        case IBinaryOpInstruction.Operator.XOR => mkXor(_lhs, _rhs)        
        case _ => sys.error("Unrecognized binary operator " + op)
      }
    case p@PureVar(typ) =>
      val name = getSolverName(p)
      typ match {
        case TypeReference.Int
           | TypeReference.Byte
           | TypeReference.Short
           | TypeReference.Char => mkIntVar(name)
        case TypeReference.Boolean | TypeReference.JavaLangObject => mkBoolVar(name)
        case _ => sys.error("Bad type for pure var " + p + ": type " + typ + " expecting " + TypeReference.Int)
      }   
    case BoolVal(v) => mkBoolVal(v)
    case IntVal(v) => mkIntVal(v)
    case CharVal(v) => mkIntVal(v.getNumericValue) 
    // TODO: add simple solver support for non-integer constants
    case _ => sys.error("Unexpected pure val " + p + " type " + p.getClass)    
  }
    
  def toAST(lhs : PureExpr, op : CmpOp, rhs : PureExpr) : T = toAST(toAST(lhs), op, toAST(rhs))
  def toAST(lhs : T, op : CmpOp, rhs : T) : T = op match {
    case IConditionalBranchInstruction.Operator.EQ => mkEq(lhs, rhs)
    case IConditionalBranchInstruction.Operator.NE => mkNe(lhs, rhs)
    case IConditionalBranchInstruction.Operator.GT => mkGt(lhs, rhs)
    case IConditionalBranchInstruction.Operator.LT => mkLt(lhs, rhs)
    case IConditionalBranchInstruction.Operator.GE => mkGe(lhs, rhs)
    case IConditionalBranchInstruction.Operator.LE => mkLe(lhs, rhs)
    case _ => sys.error("Unrecognized comparison operator " + op)  
  }
  def toConjunct(i : Iterable[PureConstraint]) : T = i.foldLeft (mkBoolVal(true)) ((ast, c) => mkAnd(toAST(c), ast))
  // TODO : fix typing issues that make this necessary
  def mkNotImpliesAssert(lhs : Iterable[PureConstraint], rhs : Iterable[PureConstraint]) : Unit = mkAssert(mkNot(mkImplies(toConjunct(lhs), toConjunct(rhs))))  
  
}