package edu.colorado.hopper.client

import java.io.File

import com.ibm.wala.classLoader.IBytecodeMethod
import com.ibm.wala.demandpa.alg.BudgetExceededException
import com.ibm.wala.ipa.callgraph.propagation.{InstanceKey, LocalPointerKey}
import com.ibm.wala.ipa.cha.ClassHierarchy
import com.ibm.wala.ssa.SSACheckCastInstruction
import com.ibm.wala.types.{ClassLoaderReference, TypeReference}
import edu.colorado.hopper.client.DowncastCheckingClient._
import edu.colorado.hopper.state.{ObjVar, PtEdge, Qry}
import edu.colorado.thresher.core.{DemandCastChecker, Options}
import edu.colorado.walautil._

import scala.collection.JavaConversions.iterableAsScalaIterable
import scala.io.Source

object DowncastCheckingClient {
  // if true, report casts as safe if they are guarded by an appropriate catch block
  val suppressCaughtExceptions = false
}

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

  def parseCastList(fileName : String) : Set[String] = 
    if (new File(fileName).exists()) {
      val f  = Source.fromFile(fileName)
      val casts = f.getLines.foldLeft (Set.empty[String]) ((set, line) => set + line)
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
    
    val castTimer = new Timer
    
    val demandFails =
      if (Options.USE_DEMAND_CAST_CHECKER) {
        val entryPoints = makeEntrypoints
        val options = makeOptions(analysisScope, entryPoints)
        val demandPair =
          DemandCastChecker.makeDemandPointerAnalysis(analysisScope, walaRes.cha.asInstanceOf[ClassHierarchy], options)
        val fails = DemandCastChecker.findFailingCasts(demandPair.fst.getBaseCallGraph(), demandPair.snd, demandPair.fst)
        println("====Done with demand cast checking====")
        fails.toSet
      } else Set.empty[String]

    // see if a list of cast queries was specified on the command line
    val queries = if (Options.CAST_QUERIES.isEmpty) Set.empty[String] else parseCastList(Options.CAST_QUERIES)
    if (!queries.isEmpty) println(s"Solving ${queries.size} queries from ${Options.CAST_QUERIES}")
    var checkedQueries = Set.empty[String]

    val exec = makeSymbolicExecutor(walaRes)
    castTimer.start

    val cha = walaRes.cha
    val pa = hg.getPointerAnalysis
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
                        !ClassUtil.isThrowableType(declaredResultType, cha)) {
                      val bytecodeMethod = node.getMethod().asInstanceOf[IBytecodeMethod]
                      // bytecode index is the only way we can get different points-to analyses to agree on which casts are the same
                      val bytecodeIndex = bytecodeMethod.getBytecodeIndex(index)
                      val castId = method + ":" + bytecodeIndex
                      val castDescr = s"class $declaringClass method ${ClassUtil.pretty(method)}} line ${IRUtil.getSourceLine(bytecodeIndex, bytecodeMethod)}"
                      print("Checking ");
                      ClassUtil.pp_instr(castInstr, node.getIR())
                      println(s" $castDescr")
                      val castPk = hm.getPointerKeyForLocal(node, castInstr.getUse(0)).asInstanceOf[LocalPointerKey]
                      val declaredResultClass = cha.lookupClass(declaredResultType)
                      val badKeys =
                        if (declaredResultClass == null) Set.empty[InstanceKey] // this can happen because of exclusions
                        else
                          pa.getPointsToSet(castPk).filter(key => !cha.isAssignableFrom(declaredResultClass,
                                                                                        key.getConcreteType()))

                      badKeys.foreach(k => assert(k.getConcreteType() != declaredResultClass, "types " + declaredResultClass + " the same!"))
                      if (!queries.isEmpty && !queries.contains(castId)) {
                        println("This query not specified by Chord; skipping")
                        (numSafe, numMightFail, numThresherProvedSafe, total)
                      } else if (badKeys.isEmpty) {
                        println("Points-to analysis proved cast #" + total + " safe.")
                        println("CAST_ID: " + castId)
                        checkedQueries = checkedQueries + castId
                        (numSafe + 1, numMightFail, numThresherProvedSafe, total + 1)
                      } else if (Options.SOUND_EXCEPTIONS && suppressCaughtExceptions && {
                        val startBlk = ir.getBasicBlockForInstruction(castInstr)
                        CFGUtil.isProtectedByCatchBlockInterprocedural(startBlk, node,
                                                                       TypeReference.JavaLangClassCastException, cg, cha)
                      }) {
                        println("Exception analysis proved cast safe.")
                        checkedQueries = checkedQueries + castId
                        (numSafe + 1, numMightFail, numThresherProvedSafe, total + 1)
                      } else {
                        println("According to point-to analysis, cast #" + total + " may fail.")
                        checkedQueries = checkedQueries + castId
                        if (Options.USE_DEMAND_CAST_CHECKER && !demandFails.contains(castId)) {
                          println("Demand cast checker proved cast #" + total + " safe.")
                          println("CAST_ID: " + castId)
                          (numSafe + 1, numMightFail, numThresherProvedSafe, total + 1)                        
                        } else if (!Options.FLOW_INSENSITIVE_ONLY) {
                          // invoke Thresher, try to show that failure can't happen
                          // query (informally): when cast occurs, local var cast doesn't point to a bad key
                          // for instr v0 = checkcast v1 T, query is v1 -> a && (a from badKeys)
                          val localEdge = PtEdge.make(castPk, ObjVar(badKeys.toSet))
                          val qry = Qry.make(List(localEdge), castInstr, node, hm, startBeforeI = true)

                          val singleCastTimer = new Timer
                          singleCastTimer.start
                          val (foundWitness, fail) =
                            try {
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
                            println("Thresher proved cast #" + total + " safe.")
                            println("CAST_ID: " + castId)
                            (numSafe, numMightFail + 1, numThresherProvedSafe + 1, total + 1)
                          } else {
                            println("Thresher cannot prove cast #" + total + " safe. Fail? " + fail)
                            ClassUtil.pp_instr(castInstr, node.getIR()); println
                            println(s"Not safe: $castId $castDescr")
                            (numSafe, numMightFail + 1, numThresherProvedSafe, total + 1)
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

    val diff = queries diff checkedQueries
    if (!diff.isEmpty) {
      println("Safe due to being unreachable:")
      diff.foreach(q => println(s"CAST_ID: $q"))
    }

    new CastCheckingResults(numSafe, numMightFail, numThresherProvedSafe)
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
                     "IteratorNoRefute", // get different results with different Java versions
                     "SwitchRefute", "SwitchNoRefute", "InfiniteLoopReturnRefute", "ListContainmentNoRefute",
                     "SwitchReturnNoRefute",
                     "HashtableEnumeratorNoRefute",
                     "HashtableEnumeratorRefute",
                     "IsInstanceRefute", "IsInstanceNoRefute",
                     "InstrOpcodeIndexSensitivePiecewiseRefute", "InstrOpcodeIndexSensitivePiecewiseNoRefute",
                     "DominatingCastRefute")

    val exceptionTests =
      Set("CatchNoRefute", "CatchRefute", "CatchNoRefuteLocal", "CatchRefuteLocal", "CatchNoRefuteLocal2",
          "CatchNoRefuteInterproc", "CatchRefuteInterproc", "CatchThrowNoRefute", "CatchThrowRefute")

    val tests = if (suppressCaughtExceptions) standardTests ++ exceptionTests else standardTests

    // results for tests whose casts are not all safe or all unsafe, or platform-specific
    val resultsMap = Util.makeMap[String,CastCheckingResults]
    // more recent versions of Java use reflection that confuses the PT analysis and make it unable to prove the safety of some easy casts
    // Thresher can't recover the lost precision, so this is now just a soundness test
    resultsMap.put("ArrayListRefute", if (javaVersion == J51) new CastCheckingResults(0, 1, 0) else new CastCheckingResults(0, 1, 1))
    resultsMap.put("IteratorNoRefute", new CastCheckingResults(4, 1, 0))
    resultsMap.put("HashtableEnumeratorRefute", new CastCheckingResults(0, 2, 2))
    resultsMap.put("HashtableEnumeratorNoRefute", new CastCheckingResults(0, 2, 1))
    resultsMap.put("DominatingCastRefute", new CastCheckingResults(0, 2, 1))
    resultsMap.put("CatchNoRefute", new CastCheckingResults(0, 1, 0))
    resultsMap.put("CatchRefute", new CastCheckingResults(1, 0, 0))

    val regressionDir = "target/scala-2.10/test-classes/casts/"
    var testNum = 0
    val pwTimeoutOk = List("ArrayListRefute")     
  
    val executionTimer = new Timer
  
    tests foreach(test => if (Options.TEST == null || Options.TEST.isEmpty() || Options.TEST == test) {
      println("Running test " + testNum + ": " + test)
      executionTimer.start
      val results = 
      try {
        val mainClass = s"Lcasts/$test/Main"
        val path = regressionDir + test
        Options.INDEX_SENSITIVITY = test.contains("IndexSensitive")
        if (!Options.JUMPING_EXECUTION && test.contains("Piecewise")) Options.JUMPING_EXECUTION = true
        if (Options.JUMPING_EXECUTION) Options.PRIM_ARRAY_SENSITIVITY = true
        if (exceptionTests.contains(test)) Options.SOUND_EXCEPTIONS = true
        else Options.SOUND_EXCEPTIONS = false
        new DowncastCheckingClient(path, Util.strToOption(Options.LIB), mainClass, "main", isRegression = true).checkCasts
      } catch {
        case e : BudgetExceededException =>
          println(s"Exceeded budget. Piecewise? ${Options.JUMPING_EXECUTION} $pwTimeoutOk")
          // for piecewise, a timeout is the expected result for some tests
          if (Options.JUMPING_EXECUTION && !pwTimeoutOk.contains(test)) resultsMap(test)
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