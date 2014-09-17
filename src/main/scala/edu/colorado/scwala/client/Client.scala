package edu.colorado.scwala.client

import java.io.{File, FileInputStream}
import java.util.jar.JarFile

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.classLoader.{BinaryDirectoryTreeModule, IClass, IMethod}
import com.ibm.wala.ipa.callgraph.AnalysisOptions.ReflectionOptions
import com.ibm.wala.ipa.callgraph.{AnalysisCache, AnalysisOptions, AnalysisScope, CGNode, CallGraph, CallGraphBuilder, CallGraphStats, ClassTargetSelector, ContextSelector, Entrypoint, MethodTargetSelector}
import com.ibm.wala.ipa.callgraph.impl.{ArgumentTypeEntrypoint, ClassHierarchyClassTargetSelector, ClassHierarchyMethodTargetSelector, DefaultEntrypoint}
import com.ibm.wala.ipa.callgraph.propagation.{HeapModel, PointerAnalysis, PointerKey, SSAContextInterpreter}
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXInstanceKeys
import com.ibm.wala.ipa.cha.{ClassHierarchy, IClassHierarchy}
import com.ibm.wala.ipa.modref.ModRef
import com.ibm.wala.ssa.{InstanceOfPiPolicy, SSAOptions}
import com.ibm.wala.types.ClassLoaderReference
import com.ibm.wala.util.config.FileOfClasses
import com.ibm.wala.util.intset.OrdinalSet
import edu.colorado.scwala.client.Client._
import edu.colorado.scwala.executor.{DefaultSymbolicExecutor, SymbolicExecutor, TransferFunctions}
import edu.colorado.scwala.piecewise.{DefaultPiecewiseSymbolicExecutor, RelevanceRelation}
import edu.colorado.scwala.synthesis.{SynthesisSymbolicExecutor, SynthesisTransferFunctions}
import edu.colorado.scwala.util.{ClassUtil, Timer, Util}
import edu.colorado.thresher.core._

import scala.collection.JavaConversions.{asJavaCollection, collectionAsScalaIterable, iterableAsScalaIterable}

object Client {
  protected val DEBUG = true
}

// simple struct to hold output of up-front WALA analysis
class WalaAnalysisResults(val cg : CallGraph, val hg : HeapGraph, val hm : HeapModel, val modRef : java.util.Map[CGNode, OrdinalSet[PointerKey]]) {
  val cha : IClassHierarchy = cg.getClassHierarchy()
  val pa : PointerAnalysis = hg.getPointerAnalysis()
}

abstract class Client(appPath : String, libPath : Option[String], mainClass : String, mainMethod : String, isRegression : Boolean = false) { 
  
  //lazy protected val analysisScope = makeAnalysisScope(isRegression)
  lazy protected val analysisScope = makeAnalysisScope()
  lazy protected val cha = ClassHierarchy.make(analysisScope)  
  
  def makeAnalysisCache : AnalysisCache = new AnalysisCache  
  
  def makeCallGraphAndPointsToAnalysis : WalaAnalysisResults = {    
    if (DEBUG) println(s"Class hierarchy size is ${cha.getNumberOfClasses()}")
    val entrypoints = makeEntrypoints
    assert(!entrypoints.isEmpty, "No entrypoints found! Class " + mainClass + " with method " + mainMethod + " does not seem to exist")
    if (DEBUG) {
      println(s"Got ${entrypoints.size} entrypoints")
      entrypoints.foreach(e => println(e.getMethod()))
    }
    val options = makeOptions(analysisScope, entrypoints)        
    val cache = makeAnalysisCache
    
    // finally, build the call graph and extract the points-to analysis
    val cgBuilder = makeCallGraphBuilder(options, cache, cha, analysisScope, isRegression)    
    // very important to do this *after* creating the call graph builder
    addBypassLogic(options, analysisScope, cha)   
    options.setSelector(makeClassTargetSelector(cha))
    options.setSelector(makeMethodTargetSelector(cha))    
    
    val ptTimer = new Timer
    ptTimer.start
    println("Building call graph")
    val cg = cgBuilder.makeCallGraph(options, null)
    ptTimer.stop
    println(s"Points-to analysis took ${ptTimer.time} seconds")
    ptTimer.clear
    if (DEBUG) println(CallGraphStats.getStats(cg))
    val pa = cgBuilder.getPointerAnalysis()
    val hg = new HeapGraphWrapper(pa, cg)
    val hm = pa.getHeapModel()
    // TODO: eventually, may not want to compute mod/ref in all situations, or even at all
    val modRef = ModRef.make
    val modRefMap = modRef.computeMod(cg, pa)    
    SameReceiverEntrypoint.clearCachedArgs()
    new WalaAnalysisResults(cg, hg, hm, modRefMap)
  }   
  
  // add bypass logic that delegates to stubs if applicable
  def addBypassLogic(options : AnalysisOptions, analysisScope : AnalysisScope, cha : IClassHierarchy) : Unit = 
    com.ibm.wala.ipa.callgraph.impl.Util.addDefaultBypassLogic(options, analysisScope, classOf[com.ibm.wala.ipa.callgraph.impl.Util].getClassLoader(), cha)
  
  // override to specify custom context interpreters and selectors
  def makeContextInterpreter(options : AnalysisOptions, cache : AnalysisCache) : SSAContextInterpreter = null
  def makeContextSelector(options : AnalysisOptions, cha : IClassHierarchy) : ContextSelector = null
  // override to specify custom method and class target selectors
  // TODO: create delegator if options.getSelector doesn't return null?
  def makeMethodTargetSelector(cha : IClassHierarchy) : MethodTargetSelector = 
    new ClassHierarchyMethodTargetSelector(cha)    
  def makeClassTargetSelector(cha : IClassHierarchy) : ClassTargetSelector =
    new ClassHierarchyClassTargetSelector(cha)   
      
  def makeCallGraphBuilder(options : AnalysisOptions, cache : AnalysisCache, cha : IClassHierarchy, 
                           analysisScope : AnalysisScope, isRegression : Boolean) : CallGraphBuilder = {
    assert(options.getMethodTargetSelector() == null, "Method target selector should not be set at this point.")
    assert(options.getClassTargetSelector() == null, "Class target selector should not be set at this point.")
    //options.setSelector(makeMethodTargetSelector(cha))
    //options.setSelector(makeClassTargetSelector(cha))
    addBypassLogic(options, analysisScope, cha)
    val defaultInstancePolicy = ZeroXInstanceKeys.ALLOCATIONS | ZeroXInstanceKeys.SMUSH_MANY | ZeroXInstanceKeys.SMUSH_STRINGS | ZeroXInstanceKeys.SMUSH_THROWABLES
    val instancePolicy = if (Options.PRIM_ARRAY_SENSITIVITY) defaultInstancePolicy else (defaultInstancePolicy | ZeroXInstanceKeys.SMUSH_PRIMITIVE_HOLDERS)
    new ImprovedZeroXContainerCFABuilder(cha, options, cache, makeContextSelector(options, cha), makeContextInterpreter(options, cache), instancePolicy)
  }
  
  def makeOptions(analysisScope : AnalysisScope, entrypoints : Iterable[Entrypoint]) : AnalysisOptions = {
    val collectionEntrypoints : java.util.Collection[_ <: Entrypoint] = entrypoints
    val options = new AnalysisOptions(analysisScope, collectionEntrypoints)
    // turn off handling of Method.invoke(), which dramatically speeds up pts-to analysis
    options.setReflectionOptions(ReflectionOptions.NO_METHOD_INVOKE)
    if (Options.USE_PI_NODES) {
      //  use WALA's pi nodes to get cheap and easy handling of instanceof guards for cast checking 
      val ssaOpt = SSAOptions.defaultOptions()
      ssaOpt.setPiNodePolicy(InstanceOfPiPolicy.createInstanceOfPiPolicy())
      options.setSSAOptions(ssaOpt)
    }
    options
  }
  
  def isEntrypointClass(c : IClass, analysisScope : AnalysisScope, mainClass : String) : Boolean = 
    // do contains(mainClass) instead of equality to account for WALA adding 'L' to front of each class name
    !ClassUtil.isLibrary(c) && c.getName().toString().contains(mainClass)
  
  def isEntrypoint(m : IMethod, cha : IClassHierarchy, mainMethod : String) : Boolean = m.getName().toString() == mainMethod
  
  // this creates concrete allocations for non-interface types and passes null (!) for interface types. potentially bad for the pt analysis
  def mkDefaultEntrypoint(m : IMethod, cha : IClassHierarchy) : Entrypoint = new DefaultEntrypoint(m, cha)
  // this always create *a* concrete allocation of and interface (if possible) to pass as arguments to the entrypoint, which is nicer for the pt analysis
  def mkArgumentTypeEntrypoint(m : IMethod, cha : IClassHierarchy) : Entrypoint = new ArgumentTypeEntrypoint(m, cha)
  // this goes one step beyond ArgumentTypeEntrypoint and passes *all* concrete allocations of an interface in scope as arguments.
  // in addition, it considers aliasing among arguments passed in externally in order to maximize the amount of behavior we see
  // this is *especially* important for Android since entrypoints are event handler methods on OS-level objects (like Activity's).
  // if we don't consider the possibility that each event handler is called on the same Activity, we will (unsoundly) miss a lot of behavior
  def mkSharedAllocationEntrypoint(m : IMethod, cha : IClassHierarchy) : Entrypoint = new SharedAllocationEntrypoint(m, cha)
  
  def mkEntrypoint(m : IMethod, cha : IClassHierarchy) : Entrypoint = {
    if (DEBUG) println(s"Making entrypoint $m")
    // IMPORTANT! for maximally evil synthesis, we want DefaultEntrypoint rather than SharedAllocationEntrypoint. this is because we don't 
    // want the analysis to assume one of the concrete types in the class hierarchy was the interface implementation that was used; 
    // we want the leeway to create our own implementation. for less adversarial synthesis, we may want to make the opposite choice 
    if (Options.SYNTHESIS) mkDefaultEntrypoint(m, cha) else mkSharedAllocationEntrypoint(m, cha)
  }
  
  def makeEntrypoints : Iterable[Entrypoint] = {    
    def addMethodsToEntrypoints(methods : Iterable[IMethod], entrypoints : List[Entrypoint]) : List[Entrypoint] = 
      methods.foldLeft (entrypoints) ((entrypoints, m) => if (isEntrypoint(m, cha, mainMethod)) mkEntrypoint(m, cha) :: entrypoints else entrypoints) 
    
    cha.foldLeft (List.empty[Entrypoint]) ((entrypoints, c) => 
      if (isEntrypointClass(c, analysisScope, mainClass)) addMethodsToEntrypoints(c.getDeclaredMethods(), entrypoints)
      else entrypoints
    )
  }
  
  def makeAnalysisScope(addJavaLibs : Boolean = true) : AnalysisScope = {
    val analysisScope = AnalysisScope.createJavaAnalysisScope()
    def isJar(f : File) : Boolean = f.getName().endsWith(".jar")
    def isClassfile(f : File) : Boolean = f.getName().endsWith(".class")
        
    def addToScope(path : String, loader : ClassLoaderReference) : Unit = {
      val f  = new File(path)
      assert(f.exists(), s"Can't find file $f; it doesn't appear to exist")
      if (f.isDirectory()) {
        // add all .class files to the scope
        analysisScope.addToScope(loader, new BinaryDirectoryTreeModule(f))
        // add all jar files in top-level directory or sub-directory to the scope
        Util.getAllFiles(f, isJar).foreach(jar => analysisScope.addToScope(loader, new JarFile(jar))) 
      } else if (isJar(f)) analysisScope.addToScope(loader, new JarFile(f))
      else if (isClassfile(f)) analysisScope.addClassFileToScope(loader, f)
      else Util.unimp(s"Processing file $f. Expecting path to directory containing Java bytecodes or a path to a JAR archive")    
    }
    
    // add application code to analysis scope
    addToScope(appPath, analysisScope.getApplicationLoader())
    // add library code to analysis scope, if any
    libPath match {
      case Some(libPath) =>
        if (DEBUG) println(s"Adding lib file $libPath")
        addToScope(libPath, analysisScope.getPrimordialLoader())
      case None =>
        if (DEBUG) println("No library code specified.")
        () // no library code specified
    }

    if (addJavaLibs) getJVMLibFile match { 
      // add core Java libraries      
      case Some(libFile) => analysisScope.addToScope(analysisScope.getPrimordialLoader(), new JarFile(libFile))
      case None => sys.error("Can't find path to Java libraries. Exiting.")
    }  
    
    val THRESHER_ASSERTS_AND_ANNOTATIONS_PATH = "../thresher/bin/edu/colorado/thresher/external"
    
    // add Thresher assertions/annotations if appropriate
    val assertsAndAnnotsFile = new File(THRESHER_ASSERTS_AND_ANNOTATIONS_PATH)
    if (assertsAndAnnotsFile.exists()) analysisScope.addToScope(analysisScope.getPrimordialLoader(), new BinaryDirectoryTreeModule(assertsAndAnnotsFile))
    
    setExclusions(analysisScope)
    analysisScope
  }
  
  // TODO: eliminate reference to options here? make WALA regression exclusions the default?
  def setExclusions(analysisScope : AnalysisScope) : Unit = {
    // set exclusions if appropriate
    val exclusionsFile = new File(Options.EXCLUSIONS)
    //val exclusionsFile = new File(Options.EXCLUSIONS)
    if (exclusionsFile.exists()) {
      if (DEBUG) println(s"Using exclusions file ${exclusionsFile.getAbsolutePath()}")
      analysisScope.setExclusions(new FileOfClasses(new FileInputStream(exclusionsFile)))           
    } else if (DEBUG) println(s"Exclusions file ${exclusionsFile.getAbsolutePath()} does not exist")
  }
  
  def makeTransferFunctions(walaRes : WalaAnalysisResults) : TransferFunctions =  
    new TransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha, walaRes.modRef)
 
  def makeSymbolicExecutor(walaRes : WalaAnalysisResults) : SymbolicExecutor = 
    if (Options.PIECEWISE_EXECUTION) { 
      val tf = makeTransferFunctions(walaRes)
      new DefaultPiecewiseSymbolicExecutor(tf, new RelevanceRelation(tf.cg, tf.hg, tf.hm, tf.cha))
    } else if (Options.SYNTHESIS) new SynthesisSymbolicExecutor(new SynthesisTransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha, walaRes.modRef))  
    else new DefaultSymbolicExecutor(makeTransferFunctions(walaRes))
  
  def getJVMLibFile : Option[File] = {    
    val PATH = System.getProperty("java.home")
    List(new File(PATH + "/lib/rt.jar"), new File(PATH + "/../Classes/classes.jar")).find(f => f.exists())
  }
    
}

abstract class ClientTests {  
  def runRegressionTests() : Unit = ()
  // is this client compatible with piecewise execution? this should be true for most refutation-oriented clients and false for most witness-oriented ones
  def isPiecewiseCompatible : Boolean = true
  
  protected def printTestFailureMsg(test : String, testNum : Int) : Unit = println(s"Test $test (#$testNum) failed :(")
  
  protected def getJVMVersion : String = System.getProperty("java.version")   


}