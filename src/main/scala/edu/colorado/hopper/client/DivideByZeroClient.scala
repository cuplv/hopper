package edu.colorado.hopper.client

import com.ibm.wala.shrikeBT.IBinaryOpInstruction
import com.ibm.wala.ssa.{SSABinaryOpInstruction, SymbolTable}
import edu.colorado.hopper.executor.{DefaultSymbolicExecutor, TransferFunctions}
import edu.colorado.hopper.state._
import edu.colorado.walautil.{ClassUtil, IRUtil}

import scala.collection.JavaConversions._

class DivideByZeroClient(appPath : String, libPath : Option[String], mainClass : String, mainMethod : String,
                         isRegression : Boolean = false)
  extends Client[(Int,Int)](appPath, libPath, mainClass, mainMethod, isRegression) {

  override def check : (Int, Int) = {
    val walaRes = makeCallGraphAndPointsToAnalysis // compute cg/points-to analysis
    val exec = new DefaultSymbolicExecutor(new TransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha))

    def isNonZeroConstant(useNum : Int, tbl : SymbolTable) : Boolean =
      tbl.isIntegerConstant(useNum) && tbl.getIntValue(useNum) != 0

    val (numUnsafe, numChecked) =
      walaRes.cg.foldLeft ((0,0)) ((countPair, n) => // for each node n in the call graph
        if (!ClassUtil.isLibrary(n)) n.getIR match { // don't analyze library code
          case null => countPair
          case ir => // for each instruction in the IR for the call graph node
            val tbl = ir.getSymbolTable
            ir.iterateAllInstructions().foldLeft (countPair) ((countPair, i) => i match {
              // find all divide instructions of the form x = y / z
              case i : SSABinaryOpInstruction if i.getOperator == IBinaryOpInstruction.Operator.DIV =>
                val srcLine = IRUtil.getSourceLine(i, ir)
                print("Checking divide instruction "); ClassUtil.pp_instr (i, ir); println(s" at line $srcLine")
                val divisorUse = i.getUse(1) // get use number of divisor
                val safe = isNonZeroConstant(divisorUse, tbl) || { // dividing by a nonzero constant c is safe
                  // query: z |-> p ^ p = 0
                  val z = Var.makeLPK(divisorUse, n, walaRes.hm)
                  val p = Pure.makePureIntVar
                  val zPtP = PtEdge.make(z, p)
                  val qry = Qry.make(List(zPtP), i, n, walaRes.hm, startBeforeI = true)
                  val pEqZero = Pure.makeEqConstraint(p, new IntVal(0))
                  qry.addPureConstraint(pEqZero)
                  val mayBeFeasible = exec.executeBackward(qry)
                  !mayBeFeasible // safe if divison by zero is infeasible
                }
                if (safe) println("Division is safe.")
                else println("Division may fail!")
                val (numUnsafe, numChecked) = countPair
                (if (!safe) numUnsafe + 1 else numUnsafe, numChecked + 1)
              case _ => countPair
            })
        } else countPair
      )

    println(s"Checked $numChecked divides, found $numUnsafe unsafe.")
    (numUnsafe, numChecked)
  }

}
