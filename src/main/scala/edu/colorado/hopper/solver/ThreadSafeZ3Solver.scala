package edu.colorado.hopper.solver

import com.microsoft.z3.{AST, ArithExpr, BoolExpr, Context, Expr, IntExpr, Status}
import edu.colorado.hopper.state.{PureExpr, PureVal, PureVar}
import edu.colorado.walautil.Types.MMap

import scala.collection.mutable.HashMap

class ThreadSafeZ3Solver extends ModelSolver[AST] {
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

  override def checkSAT : Boolean = this.synchronized { interpretSolverOutput(solver.Check) }

  override def checkSATWithAssumptions(assumes : List[String]) : Boolean =
    this.synchronized {
      interpretSolverOutput(solver.Check(assumes.map(assume => ctx.MkBoolConst(assume)).toArray))
    }

  override def push() : Unit = this.synchronized { solver.Push() }
  override def pop() : Unit = this.synchronized { solver.Pop() }

  override def getUNSATCore : String = sys.error("Unimp")

  override def dispose() : Unit = this.synchronized {
    ctx.Dispose()
  }

  private def interpretSolverOutput(status : Status) : Boolean = status match {
    case Status.UNSATISFIABLE => false
    case Status.SATISFIABLE => true
    case Status.UNKNOWN =>
      // this usually happens because of timeouts
      throw new UnknownSMTResult("Z3 decidability or timeout issue--got Status.UNKNOWN")
  }

  override def mkAssert(a : AST) : Unit = this.synchronized { solver.Assert(a.asInstanceOf[BoolExpr]) }

  override def mkNot(o : AST) : AST = this.synchronized { ctx.MkNot(o.asInstanceOf[BoolExpr]) }
  override def mkEq(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkEq(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr]) }
  override def mkNe(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkNot(ctx.MkEq(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr])) }
  override def mkGt(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkGt(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) }
  override def mkLt(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkLt(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) }
  override def mkGe(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkGe(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) }
  override def mkLe(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkLe(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) }

  override def mkAdd(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkAdd(Array(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])) }
  override def mkSub(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkSub(Array(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])) }
  override def mkMul(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkMul(Array(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])) }
  override def mkDiv(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkDiv(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) }
  override def mkRem(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkMod(lhs.asInstanceOf[IntExpr], rhs.asInstanceOf[IntExpr]) }
  override def mkImplies(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkImplies(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr]) }
  override def mkAnd(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkAnd(Array(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])) }
  override def mkOr(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkOr(Array(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])) }
  override def mkXor(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.MkXor(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr]) }

  override def mkIntVal(i : Int) : AST = this.synchronized { ctx.MkInt(i) }
  override def mkBoolVal(b : Boolean) : AST = this.synchronized { ctx.MkBool(b) }
  override def mkIntVar(s : String) : AST = this.synchronized { ctx.MkIntConst(s) }
  override def mkBoolVar(s : String) : AST = this.synchronized { ctx.MkBoolConst(s) }

  override def toAST(p: PureExpr) : AST = this.synchronized {
    p match {
      // Every time we create a name referencing a PureVar in our solver,
      // add it to a mapping so we can resolve names later.
      case p@PureVar(_) => names += (getSolverName(p) -> p)
      case _ => {}
    }
    super.toAST(p)
  }

  override def model: Option[Map[PureVar, PureVal]] = sys.error("Unimp")

  }