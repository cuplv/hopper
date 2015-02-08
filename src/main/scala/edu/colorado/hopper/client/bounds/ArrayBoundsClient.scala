package edu.colorado.hopper.client.bounds

import java.io.File

import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ssa.{SSAArrayReferenceInstruction, SSANewInstruction}
import com.ibm.wala.types.TypeReference
import edu.colorado.hopper.client.{Client, ClientTests}
import edu.colorado.hopper.jumping.RelevanceRelation
import edu.colorado.hopper.state.{Fld, IntVal, ObjVar, PtEdge, Pure, Qry, Var}
import edu.colorado.hopper.util._
import edu.colorado.thresher.core.Options
import edu.colorado.walautil.{CFGUtil, ClassUtil, IRUtil, LoopUtil, Timer, Util}

import scala.collection.JavaConversions._
import scala.io.Source

class ArrayBoundsClient(appPath : String, libPath : Option[String], mainClass : String, mainMethod : String, 
                        isRegression : Boolean = false)
  extends Client(appPath, libPath, mainClass, mainMethod, isRegression) {

  // if true, report accesses as safe if they are guarded by an appropriate catch block
  val suppressCaughtExceptions = false

  def parseProveList(fileName : String) : Set[Int] = 
    if (new File(fileName).exists()) {
      val f  = Source.fromFile(fileName)
      val proven = f.getLines.foldLeft (Set.empty[Int]) ((set, line) => 
        if (line.contains("can fail? false")) {
          val derefStr = "Array access # "
          val index = line.indexOf(derefStr)
          val numStr = line.substring(index + derefStr.length(), line.indexOf(" v"))
          set + numStr.toInt
        } 
        else set
      )
      f.close
      proven
    }
    else {
      println("prove file " + fileName + " does not exist.")
      Set.empty[Int]
    } 
  
  def checkArrayBounds() : (Int, Int) = {
    // for dacapo only
    val proveSetFile = s"out_${Options.APP.substring(Options.APP.lastIndexOf('/') + 1)}.txt"
    val proveSet = parseProveList(proveSetFile)
    println("proveSet size is " + proveSet.size)
    
    val walaRes = makeCallGraphAndPointsToAnalysis
    val tf = new ArrayBoundsTransferFunctions(walaRes)
    val exec = 
      if (Options.JUMPING_EXECUTION)
        new JumpingArrayBoundsSymbolicExecutor(tf, new RelevanceRelation(tf.cg, tf.hg, tf.hm, tf.cha))
      else new DefaultArrayBoundsSymbolicExecutor(tf)

    import walaRes._

    // don't check Dacapo harness methods
    def shouldIgnore(n : CGNode) : Boolean = n.getMethod().getDeclaringClass().getName().toString().startsWith("Ldacapo")
    
    val (failCount, total) = cg.foldLeft (0, 0) ((countPair, n) => if (!ClassUtil.isLibrary(n) && !shouldIgnore(n)) n.getIR() match {
      case null => countPair
      case ir =>
        val instrs = ir.getInstructions().toIterable
        val tbl = ir.getSymbolTable()
        instrs.collect({ case i : SSAArrayReferenceInstruction => i }).foldLeft (countPair) ((countPair, instr) => {
          // each instr contains an array reference x[i] where x points to some heap object arr 
          val arrayUse = instr.getArrayRef()
          val arrayLocal = Var.makeLPK(arrayUse, n, hm)
          val arrayRgn = PtUtil.getPt(arrayLocal, hg)
          if (arrayRgn.isEmpty) countPair // empty pt set -- don't bother to check and can't count toward total
          else if (Options.CAST > 0 && Options.CAST != countPair._2) (countPair._1, countPair._2 + 1) // hack for debugging - let us target a particular access
          else if (proveSet.contains(countPair._2)) {
            println(s"Skipping possible bounds fail # ${countPair._2 + 1} due to prove set")
            (countPair._1 + 1, countPair._2 + 1)
          } else if (Options.SOUND_EXCEPTIONS && suppressCaughtExceptions && {
            val startBlk = ir.getBasicBlockForInstruction(instr)
            CFGUtil.isProtectedByCatchBlockInterprocedural(startBlk, n,
              TypeReference.JavaLangNullPointerException, cg, this.cha)
          }) {
            println("Exception analysis proved null deref safe.")
            (countPair._1 + 1, countPair._2 + 1)
          } else {
            val (failCount, total) = countPair
            val srcLine = IRUtil.getSourceLine(instr, ir)
            print(s"Checking array access # $total "); ClassUtil.pp_instr(instr, ir); println(s" at source line $srcLine of ${ClassUtil.pretty(n)}")            
            
            val foundWitness = {
              val indexUse = instr.getIndex()
              val isIndexConstant = tbl.isConstant(indexUse)
              // if both index use and all array lengths are constants, we can try to prove this safe without using Thresher
              if (isIndexConstant && {
                val indexConst = tbl.getIntValue(indexUse)
                // for each array this instruction might refer to
                arrayRgn.forall(site => site.getCreationSites(cg).forall(pair => pair.fst.getIR().getInstructions().forall(i => i match { 
                  case i : SSANewInstruction if i.getNewSite() == pair.snd =>
                    val tbl = pair.fst.getIR().getSymbolTable()
                    val lengthUse = i.getUse(0)
                    // if the array length is a constant and is strictly greater than the index, this access is safe
                    tbl.isIntegerConstant(lengthUse) && tbl.getIntValue(lengthUse) > indexConst
                  case _ => true
                }))) && indexConst >= 0 // also ensure no obvious underflow
              }) {
                // refuted by pt analysis, no need to invoke Thresher
                println("Refuted by points-to analysis!")
                false              
              } else {                                                  
                val arrayObj = ObjVar(arrayRgn) 
                val arrayEdge = PtEdge.make(arrayLocal, arrayObj) // x -> arr
                val lengthPure = Pure.makePureIntVar
                val lengthEdge = PtEdge.make(arrayObj, Fld.ARRAY_LENGTH, lengthPure) // arr.length -> p0
                
                val qryEdges = List(arrayEdge, lengthEdge)
                val indexPure = Pure.makePureIntVar
                val qry = if (isIndexConstant) {
                  val qry = Qry.make(qryEdges, instr, n, hm, startBeforeI = true)
                  // handle case where index is a constant -- assert that the index variable is equal to the constant value
                  qry.addPureConstraint(Pure.makeEqConstraint(indexPure, Pure.makePureVal(tbl, indexUse)))
                  qry
                } else {                   
                  val indexLocal = Var.makeLPK(indexUse, n, hm)
                  val indexEdge = PtEdge.make(indexLocal, indexPure) // i -> p1                
                  Qry.make(indexEdge :: qryEdges, instr, n, hm, startBeforeI = true)          
                }
                                                
                val zero = IntVal(0)
                // axiom: the length field always holds a value greater than or equal to zero, as mandated by Java semantics
                qry.addPureConstraint(Pure.makeGeConstraint(lengthPure, zero))               
                
                // assert the conditions under which the array index is out of bounds
                // p0 >= p1; that is, i >= arr.length
                val overflow = Pure.makeGeConstraint(indexPure, lengthPure)
                qry.addPureConstraint(overflow)
                // TODO: currently only checking overflow--uncomment to check underflow as well
                // p0 < 0; that is, i < 0
                //val underflow = Pure.makeLtConstraint(indexPure, zero)
                //qry.addPureConstraint(Pure.makePureDisjunctiveConstraint(Set(overflow, underflow)))

                // invoke Thresher and check it
                try {
                  exec.executeBackward(qry)
                } catch {
                  case e : Throwable =>
                    println(s"Error on access # $total $e \n${e.getStackTraceString}")
                    if (Options.SCALA_DEBUG) throw e
                    else true // soundly assume we got a witness
                }
              } 
            }
            
            print(s"Array access # $total "); ClassUtil.pp_instr(instr, ir); println(s" at source line $srcLine of ${ClassUtil.pretty(n)} can fail? $foundWitness")
            (if (foundWitness) failCount + 1 else failCount, total + 1)
          }
        })        
    } else countPair)
    
    println(s"Checked $total array accesses; $failCount can fail")
    (failCount, total)
  }  
}

object ArrayBoundsClientTests extends ClientTests {

  override def runRegressionTests() : Unit = {  
    Options.FULL_WITNESSES = true
    Options.MAX_CALLSTACK_DEPTH = 4
    val J25 = "1.7.0_25"
    val J51 = "1.7.0_51"    
    val testedPlatforms = Set(J25, J51)
    val javaVersion = getJVMVersion
    if (!testedPlatforms.contains(javaVersion)) 
      println(s"Warning: running analysis with untested Java library version $javaVersion. Some tests may fail.")    
      
    val tests =
      List("Overflow0", "NoOverflow0", "NestedOverflow1", "NestedOverflow2", "NestedOverflow3",
           "NestedNoOverflow", "SwitchedBufsOverflow", "BufParamOverflow", "BufParamNoOverflow",
           "SystemExitNoOverflow", "SystemExitOverflow")
        //"ReverseOverflow", "ReverseNoOverflow" these don't work because they're underflow checks, not overflow checks

    val pwFailOk = List("SystemExitNoOverflow")

    val regressionDir = "target/scala-2.10/test-classes/bounds/"
    var testNum = 0
  
    val executionTimer = new Timer
  
    tests foreach(test => if (Options.TEST == null || Options.TEST.isEmpty() || Options.TEST == test) {
      println("Running test " + testNum + ": " + test)
      executionTimer.start
      val (failCount, total) = 
        try {
          val mainClass = s"Lbounds/$test/$test"
          val path = regressionDir + test
          Options.INDEX_SENSITIVITY = test.contains("IndexSensitive")
          if (!Options.JUMPING_EXECUTION && test.contains("Piecewise")) Options.JUMPING_EXECUTION = true
          if (Options.JUMPING_EXECUTION) Options.PRIM_ARRAY_SENSITIVITY = true
          new ArrayBoundsClient(path, Util.strToOption(Options.LIB), mainClass, "main", isRegression = true)
          .checkArrayBounds()
        } catch {      
          case e : Throwable =>
            printTestFailureMsg(test, testNum)
            throw e
        }
      executionTimer.stop
          
      // TODO: do something more fine-grained here, since there can be more than one array access per test
      if (test.contains("NoOverflow") || (failCount > 0 && pwFailOk.contains(test)))
        assert(failCount == 0, s"Test $test failed.")
      else
        assert(failCount != 0, s"Test $test failed.")

      println("Test " + test + " (#" + testNum + ") passed!")
      testNum += 1
        
      println("Test took " + executionTimer.time.toInt + " seconds.")
      LoopUtil.clearCaches
      executionTimer.clear
    })
  }
}