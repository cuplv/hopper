package edu.colorado.hopper.client

import java.io.File

import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.callgraph.propagation.{ConcreteTypeKey, InstanceKey}
import com.ibm.wala.ssa.{SSAFieldAccessInstruction, SSAInstruction, SSAInvokeInstruction, SSAPutInstruction, SymbolTable}
import com.ibm.wala.types.TypeReference
import edu.colorado.droidel.util.IRUtil
import edu.colorado.hopper.executor.{DefaultSymbolicExecutor, TransferFunctions}
import edu.colorado.hopper.piecewise.{DefaultPiecewiseSymbolicExecutor, RelevanceRelation}
import edu.colorado.hopper.state.{LocalPtEdge, PtEdge, Pure, PureVar, Qry, Var}
import edu.colorado.hopper.util.{CFGUtil, ClassUtil, PtUtil}
import edu.colorado.thresher.core.Options

import scala.collection.JavaConversions._
import scala.io.Source

class NullDereferenceClient(appPath : String, libPath : Option[String], mainClass : String, mainMethod : String, 
    isRegression : Boolean = false) extends Client(appPath, libPath, mainClass, mainMethod, isRegression) {

   // if true, report derefs as safe if they are guarded by an appropriate catch block
   val suppressCaughtExceptions = false

   def parseProveList(fileName : String) : Set[Int] =
    if (new File(fileName).exists()) {
      val f  = Source.fromFile(fileName)
      val proven = f.getLines.foldLeft (Set.empty[Int]) ((set, line) => 
        if (line.contains("can fail? false")) {
          val derefStr = "Deref # "
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
      println("File " + fileName + " does not exist.")
      Set.empty[Int]
    }  
  
  def checkNullDerefs() : (Int, Int) = {
    // for dacapo only
    val proveSetFile = s"out_${Options.APP.substring(Options.APP.lastIndexOf('/') + 1)}.txt"
    println(proveSetFile)
    val proveSet = parseProveList(proveSetFile)
    println("proveSet size is " + proveSet.size)
    
    val walaRes = makeCallGraphAndPointsToAnalysis
    val tf = new NullDereferenceTransferFunctions(walaRes)
    val exec = 
      if (Options.PIECEWISE_EXECUTION) new DefaultPiecewiseSymbolicExecutor(tf, new RelevanceRelation(tf.cg, tf.hg, tf.hm, tf.cha))
      else new DefaultSymbolicExecutor(tf)

    val cg = walaRes.cg
    val hm = walaRes.hm
    val cha = walaRes.cha
    val hg = walaRes.hg
    
    // don't check Dacapo harness methods
    def shouldIgnore(n : CGNode) : Boolean = n.getMethod().getDeclaringClass().getName().toString().startsWith("Ldacapo")
    
    val filteredCg = cg.filter(n => !ClassUtil.isLibrary(n) && !shouldIgnore(n) && n.getIR() != null)
    val dangerKeys = filteredCg.foldLeft (Set.empty[InstanceKey]) ((dangerKeys, n) => {
      val ir = n.getIR()
      val instrs = ir.getInstructions().toIterable
      val tbl = ir.getSymbolTable()
      // get all instructions of the form x.f = null
      instrs.foldLeft (dangerKeys) ((dangerKeys, i) => i match { 
        //case i : SSAPhiInstruction => if (0 to i.getNumberOfUses()).exists(i => tbl.isNullConstant(i)) =>
          //PtUtil.getPt(Var.makeLPK(i.getDef(), n, hm), hg) ++ dangerKeys
        case i : SSAPutInstruction if tbl.isNullConstant(i.getVal()) =>          
                    val srcLine = IRUtil.getSourceLine(i, ir)
          print(s"Creating danger key because of "); ClassUtil.pp_instr(i, ir); println(s" at source line $srcLine of ${ClassUtil.pretty(n)}")            
          val f = cha.resolveField(i.getDeclaredField())
          // get pt(x)
          val ptX = 
            if (i.isStatic()) PtUtil.getPt(hm.getPointerKeyForStaticField(f), hg) 
            else PtUtil.getPt(Var.makeLPK(i.getRef(), n, hm), hg)
          // get pt(x.f); that is, find out what else x.f can hold besides null
          PtUtil.getPtI(ptX, f, hg) ++ dangerKeys
        case _ => dangerKeys
      })
    }).filterNot(k => k.isInstanceOf[ConcreteTypeKey]) // these are too noisy
    
    println(s"Found ${dangerKeys.size} danger keys.")
    
    // TODO: could optimize with a type-based check instead of going straight to PT
    def mayHoldDangerKey(useNum : Int, n : CGNode, tbl : SymbolTable) : Boolean = {
      val locPt = PtUtil.getPt(Var.makeLPK(useNum, n, hm), hg)
      !locPt.intersect(dangerKeys).isEmpty
    }
        
    def canBeNullDeref(useNum : Int, i : SSAInstruction, n : CGNode, count : Int) : Boolean = 
      if (proveSet.contains(count)) { 
        println(s"Skipping possible null deref # ${count} due to prove set")
        false
      } else if (Options.SOUND_EXCEPTIONS && suppressCaughtExceptions && {
          val ir = n.getIR
          val startBlk = ir.getBasicBlockForInstruction(i)
          CFGUtil.isProtectedByCatchBlockInterprocedural(startBlk, n,
            TypeReference.JavaLangNullPointerException, cg, cha)
        }) {
          println("Exception analysis proved null deref safe.")
          false
      } else {
        val ir = n.getIR()
        val srcLine = IRUtil.getSourceLine(i, ir)
        print(s"Checking possible null deref # ${count} "); ClassUtil.pp_instr(i, ir); println(s" at source line $srcLine of ${ClassUtil.pretty(n)}")            
        // create the query
        val lpk = Var.makeLPK(useNum, n, hm)
        val nullPure = Pure.makePureVar(lpk)
        val locEdge = PtEdge.make(lpk, nullPure)      
        val qry = Qry.make(List(locEdge), i, n, hm, startBeforeI = true)
        qry.addPureConstraint(Pure.makeEqNullConstraint(nullPure))
        // invoke Thresher and check it
        val foundWitness = 
          try {
            exec.executeBackward(qry)
          } catch {
            case e : Throwable =>
              println(s"Error on access # $count $e \n${e.getStackTraceString}")
              if (Options.SCALA_DEBUG) throw e
              else true // soundly assume we got a witness
          }      
        print(s"Deref # $count "); ClassUtil.pp_instr(i, ir); println(s" at source line $srcLine of ${ClassUtil.pretty(n)} can fail? $foundWitness")
        foundWitness
    }    
    
    def isThisVar(useNum : Int) = useNum == 1
    
    // now, every time there is a field read of, field write to, or method call on a value in dangerKeys, we will check it           
    val (proven, total) = filteredCg.foldLeft (0, 0) ((statsPair, n) => {
      val ir = n.getIR
      val instrs = ir.getInstructions().toIterable
      val tbl = ir.getSymbolTable()
      instrs.foldLeft (statsPair) ((statsPair, i) => i match {
        case i : SSAFieldAccessInstruction if !i.isStatic() && !isThisVar(i.getRef()) && mayHoldDangerKey(i.getRef(), n, tbl) =>
          val numProven = (if (canBeNullDeref(i.getRef(), i, n, statsPair._2)) 0 else 1) + statsPair._1
          (numProven, statsPair._2 + 1)
        case i : SSAInvokeInstruction if 
          !i.isStatic() && !i.getDeclaredTarget().isInit() && !isThisVar(i.getReceiver()) && mayHoldDangerKey(i.getReceiver(), n, tbl) =>
          val numProven = (if (canBeNullDeref(i.getReceiver(), i, n, statsPair._2)) 0 else 1) + statsPair._1
          (numProven, statsPair._2 + 1)
        case _ => statsPair
      })      
    }) 
    
    println(s"Checked $total null derefs, proved $proven safe.")    
    (proven, total)
  }
}

object NullDereferenceTransferFunctions {
  private val DEBUG = true
}

class NullDereferenceTransferFunctions(walaRes : WalaAnalysisResults) 
  extends TransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha, walaRes.modRef) {
  
  override def execute(s : SSAInstruction, qry : Qry, n : CGNode) : List[Qry] = s match {
    case i : SSAFieldAccessInstruction if !i.isStatic() => // x = y.f or y.f = x
      PtUtil.getConstraintEdge(Var.makeLPK(i.getRef(), n, hm), qry.localConstraints) match {        
        case Some(LocalPtEdge(_, p@PureVar(_))) if qry.isNull(p) =>
          // y is null--we could never have reached the current program point because executing this instruction would have thrown a NPE
          if (NullDereferenceTransferFunctions.DEBUG) println("Refuted by dominating null check!")
          Nil
        case _ => super.execute(s, qry, n)
      }
    case i : SSAInvokeInstruction if !i.isStatic() => // x = y.m(...)
      PtUtil.getConstraintEdge(Var.makeLPK(i.getReceiver(), n, hm), qry.localConstraints) match {
        case Some(LocalPtEdge(_, p@PureVar(_))) if qry.isNull(p) =>
          // y is null--we could never have reached the current program point because executing this instruction would have thrown a NPE
          if (NullDereferenceTransferFunctions.DEBUG) println("Refuted by dominating null check!")
          Nil
        case _ => super.execute(s, qry, n)
      }
    case _ => super.execute(s, qry, n)
  }
}