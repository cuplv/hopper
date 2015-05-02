package edu.colorado.hopper.solver

import com.microsoft.z3.{AST, ArithExpr, BoolExpr, Context, Expr, IntExpr, Status}
import edu.colorado.hopper.state.{PureExpr, PureVal, PureVar}
import edu.colorado.walautil.Types.MMap

import scala.collection.mutable.HashMap

class ThreadSafeZ3Solver extends ModelSolver[AST] {
  val ctx : Context = new Context
  val solver = {
    val solver = ctx.mkSolver
    val params = ctx.mkParams()
    params.add("timeout", 10000)
    solver.setParameters(params)
    solver
  }

  // We maintain a mapping from Z3 names to PureVars for producing useful models
  val names : MMap[String, PureVar] = new HashMap[String, PureVar]

  override def checkSAT : Boolean = this.synchronized { interpretSolverOutput(solver.check) }

  override def checkSATWithAssumptions(assumes : List[String]) : Boolean =
    this.synchronized {
      interpretSolverOutput(solver.check(assumes.map(assume => ctx.mkBoolConst(assume)) : _*))
    }

  override def push() : Unit = this.synchronized { solver.push() }
  override def pop() : Unit = this.synchronized { solver.pop() }

  override def getUNSATCore : String = sys.error("Unimp")

  override def dispose() : Unit = this.synchronized {
    ctx.dispose()
  }

  private def interpretSolverOutput(status : Status) : Boolean = status match {
    case Status.UNSATISFIABLE => false
    case Status.SATISFIABLE => true
    case Status.UNKNOWN =>
      // this usually happens because of timeouts
      throw new UnknownSMTResult("Z3 decidability or timeout issue--got Status.UNKNOWN")
  }

  override def mkAssert(a : AST) : Unit = this.synchronized { solver.add(a.asInstanceOf[BoolExpr]) }

  override def mkNot(o : AST) : AST = this.synchronized { ctx.mkNot(o.asInstanceOf[BoolExpr]) }
  override def mkEq(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkEq(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr]) }
  override def mkNe(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkNot(ctx.mkEq(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr])) }
  override def mkGt(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkGt(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) }
  override def mkLt(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkLt(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) }
  override def mkGe(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkGe(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) }
  override def mkLe(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkLe(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) }

  override def mkAdd(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkAdd(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) }
  override def mkSub(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkSub(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) }
  override def mkMul(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkMul(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) }
  override def mkDiv(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkDiv(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr]) }
  override def mkRem(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkMod(lhs.asInstanceOf[IntExpr], rhs.asInstanceOf[IntExpr]) }
  override def mkImplies(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkImplies(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr]) }
  override def mkAnd(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkAnd(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr]) }
  override def mkOr(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkOr(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr]) }
  override def mkXor(lhs : AST, rhs : AST) : AST =
    this.synchronized { ctx.mkXor(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr]) }

  override def mkIntVal(i : Int) : AST = this.synchronized { ctx.mkInt(i) }
  override def mkBoolVal(b : Boolean) : AST = this.synchronized { ctx.mkBool(b) }
  override def mkIntVar(s : String) : AST = this.synchronized { ctx.mkIntConst(s) }
  override def mkBoolVar(s : String) : AST = this.synchronized { ctx.mkBoolConst(s) }

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