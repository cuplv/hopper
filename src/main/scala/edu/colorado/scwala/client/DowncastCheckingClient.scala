package edu.colorado.scwala.client

import java.io.File

import com.ibm.wala.classLoader.IBytecodeMethod
import com.ibm.wala.demandpa.alg.BudgetExceededException
import com.ibm.wala.ipa.callgraph.propagation.LocalPointerKey
import com.ibm.wala.ssa.SSACheckCastInstruction
import com.ibm.wala.types.{ClassLoaderReference, MethodReference, TypeReference}
import edu.colorado.scwala.state.{ObjVar, PtEdge, Qry}
import edu.colorado.scwala.util._
import edu.colorado.thresher.core.Options

import scala.collection.JavaConversions.iterableAsScalaIterable
import scala.io.Source

class CastCheckingResults(val numSafe : Int, val numMightFail : Int, val numThresherProvedSafe : Int) {
  
  override def equals(other : Any) : Boolean = other match {
    case results : CastCheckingResults => 
      this.numSafe == results.numSafe && this.numMightFail == results.numMightFail && this.numThresherProvedSafe == results.numThresherProvedSafe
    case _ => false
  }

  override def toString() : String =
    s"Num safe: $numSafe Num might fail: $numMightFail Thresher proved safe: $numThresherProvedSafe"
}

class DowncastCheckingClient(appPath : String, libPath : Option[String], mainClass : String, mainMethod : String, 
    isRegression : Boolean = false) extends Client(appPath, libPath, mainClass, mainMethod, isRegression) {

  // don't use exclusions in cast checking client. may want to change this in the future
  //override def setExclusions(analysisScope : AnalysisScope) : Unit = () 
 
  def parseCastList(fileName : String) : Set[String] = 
    if (new File(fileName).exists()) {
      val f  = Source.fromFile(fileName)
      val casts = f.getLines.foldLeft (Set.empty[String]) ((set, line) => {
        assert(!set.contains(line), "DUPLICATE: " + line)
        set + line
      })
      f.close
      casts
    }
    else {
      println("Cast file " + fileName + " does not exist.")
      Set.empty[String]
    }   
 
  def checkCasts() : CastCheckingResults = {
    val walaRes = makeCallGraphAndPointsToAnalysis
    import walaRes._

    /*walaRes.cha.foreach(c => if (!ClassUtil.isLibrary(c)) {
      println("class: " + c)
      c.getDeclaredMethods().foreach(m => {
        println("method " + m + " is static? " + m.isStatic())
      })
    })*/
    
    val castTimer = new Timer
    
    val demandFails : java.util.Map[MethodReference,Set[Int]] = if (Options.USE_DEMAND_CAST_CHECKER) {
      sys.error("Refactor this not to use Thresher")
      /*val scope = AnalysisScope.createJavaAnalysisScope()
      val entryPoints = new LinkedList[Entrypoint]     
      val cha = edu.colorado.thresher.core.Main.setupScopeAndEntrypoints(Options.APP, entryPoints, scope)
      val options = new AnalysisOptions(scope, entryPoints) 
      val demandPair = DemandCastChecker.makeDemandPointerAnalysis(scope, cha.asInstanceOf[ClassHierarchy], entryPoints, options, 
        edu.colorado.thresher.core.Main.WALA_REGRESSION_EXCLUSIONS)
      val fails = DemandCastChecker.findFailingCasts(demandPair.fst.getBaseCallGraph(), demandPair.snd, demandPair.fst)
      println("====Done with demand cast checking====")
      fails*/
    } else null
    //} else Set.empty[Pair[MethodReference,SSACheckCastInstruction]]   
    
    //val failSet = parseFailingCastList(Options.APP + "fail_casts.txt")
    //val failSet = parseFailingCastList(Options.APP + "fail_casts_bc.txt")
    //val failSet = parseFailingCastList(Options.APP + "fail_casts_piecewise_10.txt")
    //val failSet = parseCastList(Options.APP + "fail_casts_fi.txt")
    //val failSet = parseCastList(Options.APP + "fi_fail_casts.txt")
    val proveSetFile =
      if (Options.FLOW_INSENSITIVE_ONLY && !Options.USE_DEMAND_CAST_CHECKER) "none.txt" // don't use prove set
      else if (Options.USE_DEMAND_CAST_CHECKER) "prove_casts_fi.txt" // use casts proven by flow-insensitive analysis
      else if (Options.PIECEWISE_EXECUTION) "prove_casts_th.txt" // use casts proven by regular Thresher
      else "prove_casts_dc.txt" // regular Thresher case; use casts proven by demand cast checker
      
    /*  
    val pwProveSet = parseCastList(Options.APP + "prove_casts_pw.txt")
    val thProveSet = parseCastList(Options.APP + "prove_casts_th.txt")
    val pwMinusTh = pwProveSet.diff(thProveSet) // run on each of the casts that piecewise can prove, but Thresher can't
    println("pwMinusTh is " + pwMinusTh)
      */
      
    // for dacapo only
    val benchPath = Options.APP.substring(0, Options.APP.lastIndexOf('/') + 1)
    println(s"$benchPath")
    val proveSet = parseCastList(benchPath + proveSetFile)
    //val checkSet = parseCastList("both.txt").map(s => s.toInt)
    //println("checkSet size is " + checkSet.size + "; " + checkSet)    
    
    // TODO: tmp; sanity check!
    val checked = Util.makeSet[String]
    
    //println("failSet size is " + failSet.size) //+ " " + failSet)
    println("proveSet size is " + proveSet.size)
   
    val exec = makeSymbolicExecutor(walaRes)
    
    val NUM_ITERS = 1 // allow multiple runs to exploit recomputed invariant map
    var res : CastCheckingResults = null // TODO: hack!
    
    val alreadyRefuted = Util.makeSet[Int]
    
    val ITER_1_BUDGET = 10
    val ITER_2_BUDGET = 10
    
    //for (i <- 1 to NUM_ITERS) {
    //if (i == 1) Options.TIMEOUT = ITER_1_BUDGET
    //else if (i == 2) Options.TIMEOUT = ITER_2_BUDGET
    //println("doing iter " + i + " using timeout budget " + Options.TIMEOUT)
    castTimer.start

    val cha = walaRes.cha
    // DON'T CHANGE THE COUNTING SCHEME HERE! IT WILL MAKE REGRESSIONS FAIL
    val (numSafe, numMightFail, numThresherProvedSafe, total) = 
      cg.foldLeft (0, 0, 0, 0) ((quad, node) => {
        val declaringClass = node.getMethod().getReference().getDeclaringClass()
        // skip library classes
        if (!declaringClass.getClassLoader().equals(ClassLoaderReference.Primordial)) {
          node.getIR() match {
            case null => quad
            case ir => 
              ir.getInstructions().view.zipWithIndex.foldLeft (quad) ((quad, pair) => { 
                val method = node.getMethod().getReference()
                val (numSafe, numMightFail, numThresherProvedSafe, total) = quad
                val (instr, index) = pair
                instr match {
                  case castInstr : SSACheckCastInstruction =>
                    val declaredResultTypes = castInstr.getDeclaredResultTypes()
                    assert(declaredResultTypes.length == 1, 
                           "weird cast " + castInstr + " has " + declaredResultTypes.length + " result types")
                    val declaredResultType = declaredResultTypes.head
                    // skip casts to primitive types and exception types
                    if (!declaredResultType.isPrimitiveType &&
                        !ClassUtil.isThrowableType(declaredResultType, cha) && 
                        (Options.CAST < 0 || Options.CAST == total)) {
                      val bytecodeMethod = node.getMethod().asInstanceOf[IBytecodeMethod]
                      // bytecode index is the only way we can get different points-to analyses to agree on which casts are the same
                      val bytecodeIndex = bytecodeMethod.getBytecodeIndex(index)
                      val castId = method + ":" + bytecodeIndex
                      print("Checking "); ClassUtil.pp_instr(castInstr, node.getIR()) 
                      println(" in class " + declaringClass + " method " + ClassUtil.pretty(method) + 
                              " source line " + IRUtil.getSourceLine(bytecodeIndex, bytecodeMethod))//edu.colorado.thresher.core.Util.getSourceLineNumber(ir, index))
                      val castPk = hm.getPointerKeyForLocal(node, castInstr.getUse(0)).asInstanceOf[LocalPointerKey]  
                      val declaredResultClass = cha.lookupClass(declaredResultType)
                      assert(declaredResultClass != null, "Null class for " + declaredResultType)
                      val badKeys = pa.getPointsToSet(castPk).filter(key => !cha.isAssignableFrom(declaredResultClass, key.getConcreteType()))
                                              
                      badKeys.foreach(k => assert(k.getConcreteType() != declaredResultClass, "types " + declaredResultClass + " the same!"))
                      //if (!checkSet.contains(total)) {
                      if (badKeys.isEmpty ||
                          proveSet.contains(castId)) {
                        //!pwMinusTh.contains(castId)) {
                        //proveSet.contains(castId) || total < 1178) { // TMP!
                        println("Points-to analysis proved cast #" + total + " safe.")
                        println("CAST_ID: " + castId)
                        (numSafe + 1, numMightFail, numThresherProvedSafe, total + 1)
                      } else if (Options.SOUND_EXCEPTIONS && {
                          val startBlk = ir.getBasicBlockForInstruction(castInstr)
                          CFGUtil.isProtectedByCatchBlockInterprocedural(startBlk, node,
                                                                         TypeReference.JavaLangClassCastException, cg)
                        }) {
                        println("Exception analysis proved cast safe.")
                        (numSafe + 1, numMightFail, numThresherProvedSafe, total + 1)
                      } else {                        
                        println("According to point-to analysis, cast #" + total + " may fail.")
                        if (Options.USE_DEMAND_CAST_CHECKER &&                            
                            //({ val hasKey = demandFails.containsKey(method); println("fails has key? " + hasKey); !hasKey} ||
                            //{ val failCasts = demandFails.get(method); println("set " + failCasts); !failCasts.contains(index)} )) {
                            (!demandFails.containsKey(method) || !demandFails.get(method).contains(index))) {
                          println("Demand cast checker proved cast #" + total + " safe.")
                          println("CAST_ID: " + castId)
                          (numSafe + 1, numMightFail, numThresherProvedSafe, total + 1)                        
                        } else if (!Options.FLOW_INSENSITIVE_ONLY) {
                          if (alreadyRefuted.contains(total)) {
                            println("previous iter already refuted cast " + total)
                            (numSafe, numMightFail + 1, numThresherProvedSafe + 1, total + 1)
                          } else {
                          // invoke Thresher, try to show that failure can't happen
                          // query (informally): when cast occurs, local var cast doesn't point to a bad key
                          // for instr v0 = checkcast v1 T, query is v1 -> a && (a from badKeys)
                          val localEdge = PtEdge.make(castPk, ObjVar(badKeys.toSet))
                          val qry = Qry.make(List(localEdge), castInstr, node, hm, startBeforeI = true)
                          
                          //println("starting in " + node.getIR())
                          val singleCastTimer = new Timer
                          singleCastTimer.start
                          val (foundWitness, fail) =
                            try {
                              checked.add(castId)
                              // start at line BEFORE cast statement
                              (exec.executeBackward(qry), false)
                            } catch {
                              case e : Throwable =>
                                e.printStackTrace()
                                println("FAILED " + e + "\nThresher failed on cast #" + total)
                                if (Options.EXIT_ON_FAIL) throw e
                                else (true, true)
                            }
                          singleCastTimer.stop
                          exec.cleanup // clear symbolic executor caches
                          qry.cleanup // clear solver state from memory
                          
                          println("Checking cast took " + singleCastTimer.time)
                          if (!foundWitness) {
                            alreadyRefuted.add(total)
                            println("Thresher proved cast #" + total + " safe.")
                            println("CAST_ID: " + castId)
                            (numSafe, numMightFail + 1, numThresherProvedSafe + 1, total + 1)
                          } else {
                            println("Thresher cannot prove cast #" + total + " safe. Fail? " + fail)
                            println("Not safe: " + castId)
                            (numSafe, numMightFail + 1, numThresherProvedSafe, total + 1)
                          }
                          }
                        } else (numSafe, numMightFail + 1, numThresherProvedSafe, total + 1)
                      }                        
                    } else (numSafe, numMightFail, numThresherProvedSafe, total + 1)
                  case _ => quad
                }       
              })                
          }          
        } else quad
      })
    println("Total safe: " + numSafe)
    println("Total might fail: " + numMightFail)
    println("Thresher proved safe: " + numThresherProvedSafe)    
    castTimer.stop
    println("Checking all casts took " + castTimer.time + " seconds")
    
    // TMP: 
    //val didntCheck = failSet -- checked
    //val didntCheck = proveSet -- checked
    //println("DID NOT CHECK " + didntCheck.size); didntCheck.foreach(println)
    
    res = new CastCheckingResults(numSafe, numMightFail, numThresherProvedSafe)
    //}
    res
  }        
}

object DowncastCheckingClientTests extends ClientTests {

  override def runRegressionTests() : Unit = {  
    Options.FULL_WITNESSES = true
    Options.MAX_CALLSTACK_DEPTH = 4
    val J25 = "1.7.0_25"
    val J51 = "1.7.0_51"          
    val J55 = "1.7.0_55"
    val J67 = "1.7.0_67"
    val testedPlatforms = Set(J25, J51)
    val javaVersion = getJVMVersion
    if (!testedPlatforms.contains(javaVersion)) 
      println(s"Warning: running analysis with untested Java library version $javaVersion. Some tests may fail.")    
      
    val standardTests = List("BasicCastRefute", "BasicCastNoRefute", "InstanceOfRefute", "InstanceOfNoRefute",
                     "NegatedInstanceOfRefute", "NegatedInstanceOfNoRefute", "FieldCastRefute", "FieldCastNoRefute",
                     "ArrayListRefute",
                     "ArrayListNoRefute", 
                     //"IteratorRefute", // already refuted by pt-analysis with correct context-sensitivity policy; don't need Thresher                        
                     "IteratorNoRefute", // get different results with different Java version s
                     "SwitchRefute", "SwitchNoRefute", "InfiniteLoopReturnRefute", "ListContainmentNoRefute", 
                     "SwitchReturnNoRefute", 
                     "HashtableEnumeratorNoRefute",
                     //"HashtableEnumeratorRefute",
                     "InstrOpcodeIndexSensitivePiecewiseRefute", "InstrOpcodeIndexSensitivePiecewiseNoRefute")
                        //"CallTypeRefute", "CallTypeNoRefute") // will fix these later; results are sound, but not precise

    val exceptionTests =
      Set("CatchNoRefute", "CatchRefute", "CatchNoRefuteLocal", "CatchRefuteLocal", "CatchNoRefuteLocal2",
          "CatchNoRefuteInterproc", "CatchRefuteInterproc", "CatchThrowNoRefute", "CatchThrowRefute")

    val tests = standardTests ++ exceptionTests

    // results for tests whose casts are not all safe or all unsafe, or platform-specific
    val resultsMap = Util.makeMap[String,CastCheckingResults]
      // more recent versions of Java use reflection that confuses the PT analysis and make it unable to prove the safety of some easy casts
      // Thresher can't recover the lost precision, so this is now just a soundness test
    resultsMap.put("ArrayListRefute",
      if (javaVersion == J51) new CastCheckingResults(0, 1, 0) else new CastCheckingResults(0, 1, 1))
    resultsMap.put("IteratorNoRefute", 
        if (javaVersion == J51 || javaVersion == J55 || javaVersion == J67)
          new CastCheckingResults(2, 3, 0) else new CastCheckingResults(4, 1, 0))
    resultsMap.put("HashtableEnumeratorRefute", new CastCheckingResults(0, 2, 2))
    resultsMap.put("HashtableEnumeratorNoRefute", new CastCheckingResults(0, 2, 0))
    resultsMap.put("CatchNoRefute", new CastCheckingResults(0, 1, 0))
    resultsMap.put("CatchRefute", new CastCheckingResults(1, 0, 0))

    val regressionDir = "../thresher/apps/tests/casts/"
    var testNum = 0
    val pwTimeoutOk = List("ArrayListRefute")     
  
    val executionTimer = new Timer
  
    tests foreach(test => if (Options.TEST == null || Options.TEST.isEmpty() || Options.TEST == test) {
      println("Running test " + testNum + ": " + test)
      executionTimer.start
      val results = 
      try {         
        val path = regressionDir + test
        Options.INDEX_SENSITIVITY = test.contains("IndexSensitive")
        if (!Options.PIECEWISE_EXECUTION && test.contains("Piecewise")) Options.PIECEWISE_EXECUTION = true
        if (Options.PIECEWISE_EXECUTION) Options.PRIM_ARRAY_SENSITIVITY = true
        if (exceptionTests.contains(test)) Options.SOUND_EXCEPTIONS = true
        else Options.SOUND_EXCEPTIONS = false
        new DowncastCheckingClient(path, Util.strToOption(Options.LIB), "Main", "main", isRegression = true).checkCasts
      } catch {
        case e : BudgetExceededException =>
          println(s"Exceeded budget. Piecewise? ${Options.PIECEWISE_EXECUTION} $pwTimeoutOk")
          // for piecewise, a timeout is the expected result for some tests
          if (Options.PIECEWISE_EXECUTION && !pwTimeoutOk.contains(test)) resultsMap(test)
          else {
            printTestFailureMsg(test, testNum)
            throw e
          }
        case e : Throwable =>
          printTestFailureMsg(test, testNum)
          throw e
      }
      executionTimer.stop
          
      resultsMap.get(test) match {
        case Some(expectedResults) =>
          assert(results.equals(expectedResults) || pwTimeoutOk.contains(test),
                 s"test $test failed. got $results but expected $expectedResults")
        case None =>
          assert(results.numMightFail > 0)
          if (test.contains("NoRefute")) assert(results.numThresherProvedSafe == 0, "test " + test + " failed.")
          else assert(results.numThresherProvedSafe == 1 || pwTimeoutOk.contains(test), "test " + test + " failed.")
      }
      println("Test " + test + " (#" + testNum + ") passed!")
      testNum += 1
        
      println("Test took " + executionTimer.time.toInt + " seconds.")
      LoopUtil.clearCaches
      executionTimer.clear
    })
  }  
}