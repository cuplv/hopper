package edu.colorado.scwala.client

import java.io.File
import java.io.FilenameFilter
import scala.collection.JavaConversions._
import scala.sys.process._
import com.ibm.wala.classLoader.IMethod
import com.ibm.wala.ipa.callgraph.CallGraph
import com.ibm.wala.ipa.callgraph.Entrypoint
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.util.strings.Atom
import AssertionCheckingClient._
import edu.colorado.scwala.solver.Z3Solver
import edu.colorado.scwala.state.LocalPtEdge
import edu.colorado.scwala.state.Pure
import edu.colorado.scwala.state.Qry
import edu.colorado.scwala.state.Var
import edu.colorado.scwala.synthesis.DummyImplGeneratingEntrypoint
import edu.colorado.scwala.synthesis.InvokeSynthesizerException
import edu.colorado.scwala.util.ClassUtil
import edu.colorado.scwala.util.JavaUtil
import edu.colorado.scwala.util.LoopUtil
import edu.colorado.scwala.util.Timer
import edu.colorado.scwala.util.Util
import edu.colorado.thresher.core.Options
import com.ibm.wala.types.TypeReference
import com.ibm.wala.ssa.SSAInvokeInstruction
import com.ibm.wala.ssa.SSAThrowInstruction
import com.ibm.wala.types.MethodReference
import com.ibm.wala.types.ClassLoaderReference
import com.ibm.wala.types.TypeName
import com.ibm.wala.ssa.SSANewInstruction
import com.ibm.wala.ipa.callgraph.CGNode
import edu.colorado.scwala.util.IRUtil

object AssertionCheckingClient {
  def removeSynthesizedSourceAndClasses(appPath : String, generatedFiles : Iterable[String], removeSrc : Boolean = true) : Unit = generatedFiles.foreach(f => {
    // Nick's synthesizer generates the source files in the top-level directory rather than in the test directory
    val generatedSource = new File(f + ".java")
    val generatedClassDir = new File(appPath + "bin/")
    val classFiles = generatedClassDir.listFiles(new FilenameFilter {
      def accept(dir: File, name: String): Boolean = name.contains("Driver") && name.endsWith(".class")
    })
    classFiles.foreach(_.delete())
    if (generatedSource.exists()) generatedSource.delete()
  })     
}

sealed trait Assertion
case class JavaLangAssertion(i : SSANewInstruction, n : CGNode) extends Assertion 
case class CustomAssertion(i : SSAInvokeInstruction, useNum : Int, n : CGNode) extends Assertion

class AssertionCheckingClient(appPath : String, libPath : Option[String], mainClass : String, mainMethod : String, 
    isRegression : Boolean = false) extends Client(appPath, libPath, mainClass, mainMethod, isRegression) {
  
  // TODO: get queries from Java-defined assertions also by looking for "throw java/lang/AssertionError"
  type MethodSignature = String
  
  // look for custom-defined assertion functions
  private def identifyAssertionMethods(cg : CallGraph) : Set[MethodSignature] = {
    def isAsserty(name : String) : Boolean = name.contains("assert") || name.contains("Assert")

    def hasBooleanParam(m : IMethod) : Boolean =
      (0 to m.getNumberOfParameters() - 1).exists(i => m.getParameterType(i).getName() == TypeReference.Boolean.getName())

    
    cg.foldLeft (Set.empty[MethodSignature]) ((s, n) => {
      val method = n.getMethod()
      if ((isAsserty(method.getName().toString()) || isAsserty(method.getDeclaringClass().getName().toString())) &&
          hasBooleanParam(method))
        s + method.getSignature()
      else s
    })
  }
    
  val ASSERT_EXCEPTION = TypeReference.findOrCreate(ClassLoaderReference.Application, TypeName.findOrCreate("Ljava/lang/AssertionError"))
  
  private def collectAssertions(cg : CallGraph) : Iterable[Assertion] = {
    val assertMethods = identifyAssertionMethods(cg)
    println(s"Found ${assertMethods.size} custom assert methods: ")
    assertMethods.foreach(m => println(m))

    cg.foldLeft (List.empty[Assertion]) ((asserts, n) => if (!ClassUtil.isLibrary(n)) n.getIR() match {
      case null => asserts
      case ir => 
        ir.getInstructions().view.zipWithIndex.foldLeft (asserts) ((asserts, pair) => pair._1 match {
          case i : SSAInvokeInstruction if assertMethods.contains(i.getDeclaredTarget().getSignature()) =>
            val m = i.getDeclaredTarget()
            val boolParams = (0 to m.getNumberOfParameters() - 1).collect({ case i if m.getParameterType(i) == TypeReference.Boolean => i})
            assert(boolParams.size == 1, s"More than one bool param for assert method $m; not sure which one is the assertion.")
            assert(m.getParameterType(0) == TypeReference.Boolean, "Expecting first parameter of $m to be a boolean")
            CustomAssertion(i, i.getUse(boolParams.head), n) :: asserts
          case i : SSANewInstruction if i.getConcreteType() == ASSERT_EXCEPTION =>
            JavaLangAssertion(i, n) :: asserts
          case _ => asserts        
        })      
    } else asserts)
  }
  
  def checkAssertions(projectName : String) : Iterable[String] = {
    val walaRes = makeCallGraphAndPointsToAnalysis
    
    val asserts = collectAssertions(walaRes.cg)
    println(s"Collected ${asserts.size} assertions")
    
    def printResultMsg(loc : String, mayFail : Boolean) : Unit = 
      if (mayFail) println("Warning: assertion at " + loc + " may fail.")
      else println("Assertion at " + loc + " cannot fail")
    
    val exec = makeSymbolicExecutor(walaRes)
      
    asserts.foldLeft (List.empty[String]) ((synthesizedClasses, _assert) => _assert match {
      case JavaLangAssertion(instr, node) => sys.error("Checking Java assertions")
      case CustomAssertion(invoke, useNum, node) =>
        
    //asserts.foldLeft (List.empty[String]) ((synthesizedClasses, _assert) => {
      //val (invoke, node) = (_assert.fst, _assert.snd)
      val ir = node.getIR()
      
      val loc = ir.getInstructions().view.zipWithIndex.find(pair => pair._1 == invoke) match {
        case Some((instr, index)) => 
          ClassUtil.pretty(node) + ": line " + IRUtil.getSourceLine(instr, ir)
        case None => sys.error("Couldn't find assertion " + invoke + " in " + node)
      }      
      println("Checking assertion at " + loc)
      
      val tbl = ir.getSymbolTable()
      val constantRetval = tbl.isConstant(invoke.getUse(0))
      // handle trivial assert(true) case
      if (constantRetval && tbl.getIntValue(invoke.getUse(0)) != 0) {
        printResultMsg(loc, false)
        synthesizedClasses
      } else {
        val hm = walaRes.hm
        // assertion is x = assert(y). create y == false query; that is, a query expressing that
        // the assertion *does* fail. we will try to refute this query.
        val qry = if (constantRetval) Qry.make(Nil, invoke, node, hm, startBeforeI = true) // y == false. assert(false) case
        else { // normal assert(y) case
          val assertArg = Var.makeLocalVar(invoke.getUse(0), node, hm)
          val falseVal = Pure.makePureVar(assertArg.key)
          val q = Qry.make(List(LocalPtEdge(assertArg, falseVal)), invoke, node, hm, startBeforeI = true)        
          q.addPureConstraint(Pure.makeEqBoolConstraint(falseVal, false))
          q
        }

        val assertTimer = new Timer
        assertTimer.start
        val newSynthesizedClasses = try {   
          val foundWitness = exec.executeBackward(qry)
          assert(!foundWitness, "Found witness, but no exception was thrown to invoke the synthesizer")
          printResultMsg(loc, foundWitness)
          synthesizedClasses
        } catch {
          case InvokeSynthesizerException(path) =>
            val qry = path.qry
            // TODO: maybe we don't want to put synthesized classes in the pwd?
            val pwd = new File(System.getProperty("user.dir"))
            val logger = println(_: String)
            try {
              sys.error("Fix Nick's synthesizer")
              synthesizedClasses /*++ FreeMonadSynthesizer.unsafePerform(pwd, logger,
                FreeMonadSynthesizer.synthesize(
                    new Z3Solver,
                    projectName,
                    qry.node.getMethod(),
                    qry.localConstraints ++ qry.heapConstraints,
                    qry.pureConstraints))*/
            } /*catch {
              case e@FreeMonadSynthesizer.SynthesisException(msg) => {
                println(s"Error during synthesis: $msg")
                throw e
              }
            }*/
           case e : Throwable =>
            e.printStackTrace()
            println("FAILED " + e + "\nThresher failed while checking assert at " + loc)
            if (Options.EXIT_ON_FAIL) throw e
            synthesizedClasses
        }
        assertTimer.stop
        exec.cleanup // clear symbolic executor caches
        qry.cleanup // clear solver state from memory
        newSynthesizedClasses
      }
    })
  }   
  
  // use special entrypoint that generates dummy implementations for interface types
  override def mkEntrypoint(m : IMethod, cha : IClassHierarchy) : Entrypoint = 
    new DummyImplGeneratingEntrypoint(m, cha, useExistingImpls = false)                  
}

object AssertionCheckingClientTests extends ClientTests {
  
  override def runRegressionTests : Unit = {
    Options.SYNTHESIS = true
     val thresherRegressionDir = "../thresher/apps/tests/synthesis/"
     val scwalaRegressionDir = "test/synthesis"
     val GENERATED_TEST_NAME = "ThresherGeneratedTest"
     val ASSERTION_FAILURE = "java.lang.NullPointerException: Failed assertion!"
     val tests = List("TrueAssertionNoTest", "FalseAssertion", "InputOnly", "MultiInput", "SimpleInterface", 
                      "SimpleInterfaceIrrelevantMethod", "SimpleInterfaceTwoMethods", "SimpleInterfaceNullObject",
                      "SimpleInterfaceObject", "MixedObjAndInt", "SimpleField", "Nested", "NestedField")//, "FakeMap", "ArrayMap")
      
     var testNum = 0
     var successes = 0
     var failures = 0
     val executionTimer = new Timer
     tests foreach (test => if (Options.TEST == null || Options.TEST.isEmpty() || Options.TEST == test) {
       testNum += 1
       println("Running test " + testNum + ": " + test)
       executionTimer.start
       try {
         val (mainClass, mainMethod) = {
           // TODO: allow the command-line options for main class and main method to be used
           if (test.contains("FakeMap")) ("FakeMap", "<init>")
           else if (test.contains("ArrayMap")) ("ArrayMap", Options.MAIN_METHOD)
           else ("Main", "foo")
         }
         val path = {
           val thresherTestPath = s"$thresherRegressionDir$test"
           if (new File(thresherTestPath).exists()) thresherTestPath // it's a Thresher test
           else s"$scwalaRegressionDir$test" // it's (hopefully) a scwala test
         }
         //val path = regressionDir + test
         Options.INDEX_SENSITIVITY = test.contains("IndexSensitive")
         val synthesizedClasses = 
           new AssertionCheckingClient(path, Util.strToOption(Options.LIB), mainClass, mainMethod, isRegression = true).checkAssertions(test)
         // tests with NoTest contain assertions that cannot fail, so no code should be synthesized
         if (test.contains("NoTest")) {
           assert(synthesizedClasses.isEmpty)
           println("Test " + test + " (#" + testNum + ") passed!")
         } else { // compile the synthesized classes
           val filename = path + "/"
           val binDir = filename + "bin"
           val compilerOptions = List("-d", binDir, "-cp", filename + ":" + binDir)
                     
           if (JavaUtil.compile(synthesizedClasses, compilerOptions)) { // compilation succeeded; now run the test
             // TODO: this is not the best way to do this--would be better to dynamically load compiled class and reflectively invoke the harness method of the generated test
             // it would be cleanest to have the synthesized code declare a boolean type method that try/catches the AssertionFailedException and returns true iff the assertion fails dynamically
             println("Compiled generated test.")
             var output = ""
             val cmd = "java -cp " + ".:bin/:" + binDir + ":../thresher/bin " + synthesizedClasses.head
             // run cmd in shell and collect stderr/stdout
             cmd lines_! ProcessLogger(line => output += line)
             
             if (output != null && output.contains(ASSERTION_FAILURE)) { // running generated test triggered assertion failure
               println("Generated test caused assertion failure!")
               println("Test " + test + " (#" + testNum + ") passed!")                
             } else { // generated test did not trigger assertion failure
               // TODO: re-try synthesis or re-invoke Thresher here? lots of interesting choices
               println("Generated test did not cause assertion failure.")
               println("Test " + test + " (#" + testNum + ") failed :(")
               // delete all the synthesized sources and their classfiles
               removeSynthesizedSourceAndClasses(filename, synthesizedClasses, removeSrc = false)  
               if (Options.EXIT_ON_FAIL) System.exit(1)                            
             }                             
            } else { // compilation failed
              println("Compilation of synthesized code failed for test " + test + " (#" + testNum + ")")
              // delete all the synthesized sources and their classfiles
              removeSynthesizedSourceAndClasses(filename, synthesizedClasses, removeSrc = false)  
              if (Options.EXIT_ON_FAIL) System.exit(1)
            }
            // delete all the synthesized sources and their classfiles
            removeSynthesizedSourceAndClasses(filename, synthesizedClasses)            
          }             
        } catch {
          case e : Throwable => {
            println("Test " + test + " (#" + testNum + ") failed :(")
            throw e
          }
        }
        executionTimer.stop
                
        println("Test took " + executionTimer.time.toInt + " seconds.")
        LoopUtil.clearCaches
        executionTimer.clear
      })   
    }
    
    // synthesis and piecewise are incompatible, since synthesis is about finding witnesses and piecewise is about finding refutations
    override def isPiecewiseCompatible : Boolean = false
  }