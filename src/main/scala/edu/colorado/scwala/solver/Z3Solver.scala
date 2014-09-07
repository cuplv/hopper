package edu.colorado.scwala.solver

import scala.Array.fallbackCanBuildFrom
import scala.collection.mutable.HashMap
import com.microsoft.z3.AST
import com.microsoft.z3.ArithExpr
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.IntExpr
import com.microsoft.z3.IntNum
import com.microsoft.z3.Status
import edu.colorado.scwala.state.BoolVal
import edu.colorado.scwala.state.IntVal
import edu.colorado.scwala.state.PureVal
import edu.colorado.scwala.state.PureVar
import edu.colorado.scwala.util.Types.MMap
import edu.colorado.scwala.state.PureExpr

class Z3Solver extends ModelSolver[AST] {    
  val ctx : Context = new Context
  val solver = {    
    val solver = ctx.MkSolver
    val params = ctx.MkParams()
    params.Add("soft_timeout", 10000)
    solver.setParameters(params)
    solver
  }
  
  // We maintain a mapping from Z3 names to PureVars for producing useful models
  val names : MMap[String, PureVar] = new HashMap[String, PureVar]
  
  override def checkSAT : Boolean = interpretSolverOutput(solver.Check)
  
  override def checkSATWithAssumptions(assumes : List[String]) : Boolean =
    interpretSolverOutput(solver.Check(assumes.map(assume => ctx.MkBoolConst(assume)).toArray))

  override def push() : Unit = solver.Push()
  override def pop() : Unit = solver.Pop()

  // TMP! find some way to translate this back into pure constraints
  override def getUNSATCore : String = { 
    val unsats = solver.UnsatCore().foldLeft (List.empty[String]) ((l, s) => s.toString() :: l)
    println("UNSAT: " + unsats)
    solver.Assertions().foreach(e => {
      println("unsats have " + e)
      if (unsats.contains(e.toString)) println(e.toString())
    })
    ""
  }
  
  override def dispose() : Unit = ctx.Dispose()
    
  private def interpretSolverOutput(status : Status) : Boolean = status match {
    case Status.UNSATISFIABLE => false
    case Status.SATISFIABLE => true
    case Status.UNKNOWN =>
      sys.error("Z3 decidability issue--got Status.UNKNOWN")
      //println("Z3 decidability issue -- conservatively assuming SAT")
      //true
  } 
  
  override def mkAssert(a : AST) : Unit = solver.Assert(a.asInstanceOf[BoolExpr])
  
  override def mkNot(o : AST) : AST = ctx.MkNot(o.asInstanceOf[BoolExpr])
  override def mkEq(lhs : AST, rhs : AST) : AST = ctx.MkEq(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr]) 
  override def mkNe(lhs : AST, rhs : AST) : AST = ctx.MkNot(ctx.MkEq(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr])) 
  override def mkGt(lhs : AST, rhs : AST) : AST = ctx.MkGt(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) 
  override def mkLt(lhs : AST, rhs : AST) : AST = ctx.MkLt(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) 
  override def mkGe(lhs : AST, rhs : AST) : AST = ctx.MkGe(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) 
  override def mkLe(lhs : AST, rhs : AST) : AST = ctx.MkLe(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])
  
  override def mkAdd(lhs : AST, rhs : AST) : AST = ctx.MkAdd(Array(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])) 
  override def mkSub(lhs : AST, rhs : AST) : AST = ctx.MkSub(Array(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]))
  override def mkMul(lhs : AST, rhs : AST) : AST = ctx.MkMul(Array(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]))
  override def mkDiv(lhs : AST, rhs : AST) : AST = ctx.MkDiv(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) 
  override def mkRem(lhs : AST, rhs : AST) : AST = ctx.MkMod(lhs.asInstanceOf[IntExpr], rhs.asInstanceOf[IntExpr])
  override def mkImplies(lhs : AST, rhs : AST) : AST = ctx.MkImplies(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])
  override def mkAnd(lhs : AST, rhs : AST) : AST = ctx.MkAnd(Array(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr]))
  override def mkOr(lhs : AST, rhs : AST) : AST = ctx.MkOr(Array(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr]))
  override def mkXor(lhs : AST, rhs : AST) : AST = ctx.MkXor(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])
     
  override def mkIntVal(i : Int) : AST = ctx.MkInt(i)
  override def mkBoolVal(b : Boolean) : AST = ctx.MkBool(b)
  override def mkIntVar(s : String) : AST = ctx.MkIntConst(s)
  override def mkBoolVar(s : String) : AST = ctx.MkBoolConst(s)
  
  override def toAST(p: PureExpr) : AST = {
    p match {
      // Every time we create a name referencing a PureVar in our solver,
      // add it to a mapping so we can resolve names later.
      case p@PureVar(_) => names += (getSolverName(p) -> p)
      case _ => {}
    }
    super.toAST(p)
  }
  
  private def z3ExprToPureVal(e: Expr): PureVal = e match {
    case (e: IntNum) => IntVal(e.Int())
    case (e: BoolExpr) => BoolVal(e.IsTrue())
  }
  
  override def model: Option[Map[PureVar, PureVal]] = solver.Check match {
    case Status.SATISFIABLE => Some({
      val m = solver.Model
      Map() ++ m.ConstDecls.flatMap(decl => {
        val name = decl.Name
        val value = m.Eval(ctx.MkIntConst(name), true)
        names.get(name.toString()) match {
          case Some(purevar) => {
            val pureval = z3ExprToPureVal(value)
            List((purevar, pureval))
          }
          case _ => List()
        }
      })
    })
    case _ => None
  }
}