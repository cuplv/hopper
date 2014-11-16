package edu.colorado.hopper.driver

import java.io.File

import edu.colorado.hopper.client.{AssertionCheckingClient, AssertionCheckingClientTests, DowncastCheckingClient, DowncastCheckingClientTests, NullDereferenceClient}
import edu.colorado.hopper.client.android.{AndroidLeakClient, AndroidLeakClientTests, AndroidUIClient}
import edu.colorado.hopper.client.bounds.{ArrayBoundsClient, ArrayBoundsClientTests}
import edu.colorado.hopper.util.Util
import edu.colorado.thresher.core.Options

object Main {
  
  type MSet[T] = scala.collection.mutable.Set[T]
  
  val REGRESSION = "__regression"
    
  def main(args: Array[String]) : Unit = {     
    val target = Options.parseArgs(args)          
    
    if (target == null) println("No analysis targets given...exiting.")
    else if (target.equals(REGRESSION)) {
            
      val clientTests = 
        if (Options.CHECK_ANDROID_LEAKS) List(AndroidLeakClientTests)
        else if (Options.CHECK_CASTS) List(DowncastCheckingClientTests)
        else if (Options.CHECK_ASSERTS) List(AssertionCheckingClientTests)
        else if (Options.CHECK_ARRAY_BOUNDS) List(ArrayBoundsClientTests)
        //else List(AndroidLeakClientTests, DowncastCheckingClientTests, AssertionCheckingClientTests, ArrayBoundsClientTests)
        // TODO: bring back AssertionCheckingClientTests once we fix Nick's synthesizer
        else List(AndroidLeakClientTests, DowncastCheckingClientTests, ArrayBoundsClientTests)
      
      val singleTest = Options.TEST
      def runTests(runPiecewise : Boolean = false) : Unit = clientTests.foreach(client => {
        Options.PIECEWISE_EXECUTION = runPiecewise
        Options.SCALA_DEBUG = true
        Options.TEST = singleTest
        if (client.isPiecewiseCompatible || !runPiecewise) {
          println(s"Running tests for client ${client.getClass.getName()}")
          client.runRegressionTests
          Options.restoreDefaults() // reset default values for option flags, including PIECEWISE_EXECUTION
        }             
      })
      
      val runPiecewise = Options.PIECEWISE_EXECUTION      
      // run tests without piecewise      
      println("Running regular tests")
      runTests()
      if (runPiecewise) { // run tests with piecewise 
        println("Running piecewise tests")
        runTests(runPiecewise = true)
      }
    } else if (Options.CHECK_CASTS) {
      Options.PRINT_REFS = false
      Options.EXIT_ON_FAIL = false
      new DowncastCheckingClient(Options.APP, Util.strToOption(Options.LIB), Options.MAIN_CLASS, Options.MAIN_METHOD)
      .checkCasts()
    } else if (Options.CHECK_ANDROID_LEAKS)
      new AndroidLeakClient(Options.APP, Util.strToOption(Options.LIB), "Landroid/app/Activity", Options.MAIN_METHOD)
      .checkAnnotations
    else if (Options.CHECK_ARRAY_BOUNDS) 
      new ArrayBoundsClient(Options.APP, Util.strToOption(Options.LIB), Options.MAIN_CLASS, Options.MAIN_METHOD)
      .checkArrayBounds
    else if (Options.CHECK_ASSERTS) 
      new AssertionCheckingClient(Options.APP, Util.strToOption(Options.LIB), Options.MAIN_CLASS, Options.MAIN_METHOD)
      .checkAssertions(Options.APP)
    else if (Options.CHECK_NULLS)
      new NullDereferenceClient(Options.APP, Util.strToOption(Options.LIB), Options.MAIN_CLASS, Options.MAIN_METHOD)
      .checkNullDerefs
    else if (Options.CHECK_ANDROID_UI) {
      new AndroidUIClient(Options.APP, new File(Options.ANDROID_JAR))
      .doUICheck
      /*val topLevelAppDir = {
        val f = new File(Options.APP)        
         f.getAbsolutePath().replace(f.getParentFile().getAbsolutePath(), "") match {
           case str if str.startsWith("/") => str.substring(1)
           case str => str
        }
      }
      
      val harness = 
        if (Options.MAIN_CLASS != "Main" && Options.MAIN_METHOD != "main") Some(Options.MAIN_CLASS, Options.MAIN_METHOD)
        else None
      
      val client = new AndroidUIClient(Options.APP, new File(Options.ANDROID_JAR), harness, useJPhantom = true, useGeneratedHarness = Options.USE_GENERATED_HARNESS)
      val walaRes = client.buildAndroidCG(genHarness = Options.GEN_HARNESS, cleanupGeneratedFiles = false)
      new Absurdities(client.harnessClassName).getAbsurdities(walaRes, doXmlOutput = true)*/
    } else println("No clients given. Exiting.")
  }         
}
