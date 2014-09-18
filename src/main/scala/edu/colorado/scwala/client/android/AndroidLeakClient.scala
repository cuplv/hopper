package edu.colorado.scwala.client.android

import scala.collection.JavaConversions.asJavaCollection
import scala.collection.JavaConversions.asScalaBuffer
import scala.collection.JavaConversions.asScalaSet
import scala.collection.JavaConversions.bufferAsJavaList
import scala.collection.JavaConversions.collectionAsScalaIterable
import scala.collection.JavaConversions.iterableAsScalaIterable
import scala.collection.JavaConversions.mutableSetAsJavaSet
import scala.collection.JavaConversions.seqAsJavaList
import com.ibm.wala.classLoader.IClass
import com.ibm.wala.classLoader.IField
import com.ibm.wala.demandpa.alg.BudgetExceededException
import com.ibm.wala.ipa.callgraph.propagation.AbstractTypeInNode
import com.ibm.wala.ipa.callgraph.propagation.AllocationSiteInNode
import com.ibm.wala.ipa.callgraph.propagation.ArrayContentsKey
import com.ibm.wala.ipa.callgraph.propagation.ConcreteTypeKey
import com.ibm.wala.ipa.callgraph.propagation.InstanceFieldKey
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey
import com.ibm.wala.ipa.callgraph.propagation.PointerKey
import com.ibm.wala.ipa.callgraph.propagation.StaticFieldKey
import com.ibm.wala.types.ClassLoaderReference
import com.ibm.wala.types.TypeReference
import com.ibm.wala.types.annotations.Annotation
import com.ibm.wala.util.graph.Graph
import com.ibm.wala.util.graph.traverse.DFS
import edu.colorado.scwala.client.WalaAnalysisResults
import edu.colorado.scwala.piecewise.RelevanceRelation
import edu.colorado.scwala.solver.Z3Solver
import edu.colorado.scwala.state.CallStack
import edu.colorado.scwala.state.Fld
import edu.colorado.scwala.state.HeapPtEdge
import edu.colorado.scwala.state.ObjVar
import edu.colorado.scwala.state.PtEdge
import edu.colorado.scwala.state.PureConstraint
import edu.colorado.scwala.state.Qry
import edu.colorado.scwala.state.Path
import edu.colorado.scwala.util.ClassUtil
import edu.colorado.scwala.util.LoopUtil
import edu.colorado.scwala.util.Timer
import edu.colorado.scwala.util.Util
import edu.colorado.thresher.core.HeapGraphWrapper
import edu.colorado.thresher.core.Options
import edu.colorado.scwala.util.Types._
import edu.colorado.scwala.client.ClientTests
import com.ibm.wala.ipa.callgraph.AnalysisScope

class AndroidLeakClient(appPath : String, libPath : Option[String], mainClass : String, mainMethod : String, 
  isRegression : Boolean = false) extends AndroidClient(appPath, libPath, mainClass, mainMethod, isRegression) {
  
  // TODO: richer return type!
  def checkAnnotations() : Boolean = {
    val walaRes = makeCallGraphAndPointsToAnalysis
    
    val cha = walaRes.cha
    val NO_STATIC_REF = TypeReference.findOrCreate(ClassLoaderReference.Application, 
                        "Ledu/colorado/thresher/external/Annotations$noStaticRef")
                        
    // field errors we see in almost every app and do not want to repeatedly re-refute
    val BLACKLIST = Set("EMPTY_SPANNED", "sThreadLocal", "sExecutor", "sWorkQueue", "sHandler", "CACHED_CHARSETS")
   
    // mutable set of static fields to be populated
    val staticFields = Util.makeSet[IField]
    
    // find all subclasses of the annotatedClasses
    val snkClasses = {
      val targetClasses = { 
        // add Activity class if this is the leak client
        if (Options.ANDROID_LEAK) {
          val targetClass = cha.lookupClass(TypeReference
              .findOrCreate(ClassLoaderReference.Application, mainClass))
          if (Options.CHECK_ASSERTS) assert(targetClass != null, "couldn't find base class " + targetClass)
          List(targetClass)
        } else List.empty[IClass]
      }
   
      // find static fields and @noStaticRef annotations of each class
      val annotatedClasses = 
        cha.foldLeft (targetClasses) ((l : List[IClass], c : IClass) => {
          if (!isRegression || c.getName().toString().contains(mainClass)) {
            // populate static fields
            staticFields.addAll(c.getAllStaticFields())
          }
          val supportedAnnotsFilter = (a : Annotation) => a.getType().equals(NO_STATIC_REF)
          c.getAnnotations().find(supportedAnnotsFilter) match { 
            case Some(_) => c :: l
            case _ => l
          }
        })
      // compute sub-classes of all annotated classes
      annotatedClasses.foldLeft (Set.empty[IClass]) ((s : Set[IClass], c : IClass) =>   
        s + c ++ cha.computeSubClasses(c.getReference()))
    }
      
    // filter out fields in the blackList
    val filteredStaticFields = staticFields.filterNot((f : IField) => BLACKLIST.contains(f.getName().toString()))
    val leakList = getLeakPairs(snkClasses, filteredStaticFields, walaRes)
    println("Found " + leakList.size + " possible leaks.")
    
    val refuteStart = System.currentTimeMillis()
    val mayFail = 
      if (!Options.FLOW_INSENSITIVE_ONLY) refuteFieldErrors(leakList, walaRes)
      else false            
    val refuteEnd = System.currentTimeMillis()
    println("Symbolic execution completed in " + ((refuteEnd - refuteStart) / 1000.0) + " seconds. May fail? " + mayFail)
    //Util.Print("Total time was " + ((refuteEnd - start) / 1000.0) + " seconds")
    println("Done with " + appPath)
    mayFail
  }
 
  /**
   * @return list of (fld, node) pairs where fld is an IField in staticFields and 
   * node is an InstanceKey that may leak via fld according to the heap graph
   * 
   */
  def getLeakPairs(snkClasses : Iterable[IClass], staticFields : Iterable[IField], walaRes : WalaAnalysisResults) :
    Iterable[(PointerKey,InstanceKey)] = {
    import walaRes._
    // find nodes in the heap graph that are reachable from f and have the types of one of the classes in snkClass
    val filter = { node : Object => 
      (node.isInstanceOf[ConcreteTypeKey] && snkClasses.contains(node.asInstanceOf[ConcreteTypeKey].getConcreteType())) ||
      (node.isInstanceOf[AllocationSiteInNode] && snkClasses.contains(node.asInstanceOf[AllocationSiteInNode].getConcreteType()))
    }    
    staticFields.flatMap((f : IField) => {
      val ptrKey = hm.getPointerKeyForStaticField(f)
      if (hg.getNumber(ptrKey) != -1) {
        DFS.getReachableNodes(hg.asInstanceOf[Graph[Object]], List(ptrKey)).toSet
        .filter(filter)
        // (static field, node that may leak via field) pair
        .map((node : Any) => (ptrKey, node.asInstanceOf[InstanceKey]))
      } else List.empty[(PointerKey, InstanceKey)] // pointer key not in heap graph; can happen if it is a primitive type
    })      
  }
  
  def refuteFieldErrors(errs : Iterable[(PointerKey,InstanceKey)], walaRes : WalaAnalysisResults) : Boolean = {
    val relRelation = new RelevanceRelation(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)
    val producedEdges = Util.makeSet[PtEdge]
    val refutedEdges = Util.makeSet[PtEdge]
    // TODO: fix this. makes no sense if there are multiple alarms, and we should return something richer
    //val logger = new Logger()
    errs.foldLeft (false) ((mayFail, pair) => { 
      val (fld, key) = pair
      if (refuteFieldErrorForward(fld, key, producedEdges, walaRes, relRelation, refutedEdges)) {
        println("successfully refuted error path " + fld + " -> ... -> " + key)
        mayFail || false
      } else {
        println("successfully witnessed error path " + fld + " -> ... -> " + key)
        mayFail || true
      }})
  }
  
  // TODO: this super ugly and should be totally redone
  def refuteFieldErrorForward(srcKey : PointerKey, snkKey : InstanceKey, producedEdges : MSet[PtEdge], 
                          walaRes : WalaAnalysisResults, relRelation : RelevanceRelation, refutedEdges : MSet[PtEdge]) : Boolean = {
    val hg = walaRes.hg//import walaRes._
    var witnessedCount = 0
    val hgWrapper = hg.asInstanceOf[HeapGraphWrapper]
    var errorPath = edu.colorado.thresher.core.AndroidLeakClient.findNewErrorPath(hgWrapper, srcKey, snkKey, cha)
    if (errorPath == null) {
      println("Edges refuted on previous error preclude us from finding path! this error infeasible")
      return true
    }
    errorPath = errorPath.reverse
    
    while (errorPath != null) {
      var srcIndex = 1
      var snkIndex = 0
      var fldKey : PointerKey = null
      var newPath = false
      while (srcIndex < errorPath.size() && !newPath) {
        val snk = errorPath.get(srcIndex)
        if (snk.isInstanceOf[PointerKey] && !(snk.isInstanceOf[StaticFieldKey])) {
          // src is intermediate point in points-to edge; either instance field or array contents
          fldKey = snk match {
            case arr : ArrayContentsKey => arr
            case fld : InstanceFieldKey => fld
            case _ => sys.error("UNSUPPORTED POINTER KEY TYPE " + snk) 
          }
          srcIndex += 1
        } else {
          val snkVal = snk match {
            case k : InstanceKey => ObjVar(Set(k))
            case other => sys.error("Unexpected type for snk " + other)
          }
          
          val witnessMe = errorPath.get(snkIndex) match {
            case k : StaticFieldKey => PtEdge.make(k, snkVal)
            case k : InstanceKey =>
              val fld = Fld.make(fldKey, cha)
              PtEdge.make(ObjVar(Set(k)), fld, snkVal)
            case other => sys.error("Unexpected type for src: " + other)
          }
          
          if (!producedEdges.contains(witnessMe)) {
            val witnessed = {
              if (refutedEdges.contains(witnessMe)) {
                println("already refuted edge " + witnessMe)
                false
              } else {
                println("ATTEMPTING TO REFUTE EDGE " + witnessMe)
                println("%%%%%%%%%%%%%%%%%Starting on edge " + witnessMe + "%%%%%%%%%%%%%%%%%")
                val start = System.currentTimeMillis()                    
                val witnessed = generateWitness(witnessMe, walaRes, relRelation)
                println("Edge took " + ((System.currentTimeMillis() - start) / 1000.0) + " seconds.")
                edu.colorado.thresher.core.WALACFGUtil.clearCaches()
                witnessed
              }
            }
            if (witnessed) {
              println("Successfully produced " + witnessMe + 
                  "; done with " + witnessedCount + " of " + errorPath.size())
              witnessedCount += 1
              producedEdges.add(witnessMe)
            } else {
              // edge refuted
              witnessedCount = 0
              refutedEdges.add(witnessMe)
              Util.Assert(fldKey != null)
              hgWrapper.addIgnoreEdge(fldKey, snk)
              println("Successfully refuted edge " + witnessMe + "; now trying to find error path  without it")
              errorPath =
                edu.colorado.thresher.core.AndroidLeakClient.findNewErrorPath(hgWrapper, srcKey, snkKey, cha)
              
              if (errorPath != null) {
                println("refuted edge, but err path still exists; size " + errorPath.size())
                errorPath = errorPath.reverse
                newPath = true
              } else {
                println("no path found!")
                return true
              }
            }
          } else {
            println("already produced " + witnessMe);
          }
          fldKey = null;
          snkIndex = srcIndex
          srcIndex += 1
        } // end of producedEdges.contains(witnessMe) else block
      } // end of srcIndex < errorPath.size() witness generation loop
      // ended loop without refuting an edge; we have witnessed entire error path
      if (!newPath) {
        if (Options.SCALA_DEBUG) println("error is real! we have witnessed entire path");
        if (Options.DUMP_WITNESSED_ERR_PATHS) {
            println("<Err Path>")
            errorPath.foreach(println)
            println("</Err Path>")
        }
        return false
      }      
    } // end of "while path exists" loop
    // error path is null; we have a refutation!
    return true
  }
 
  // TODO: this is horrible and should be totally rewritten 
  def generateWitness(witnessMe : PtEdge, walaRes : WalaAnalysisResults, relRelation : RelevanceRelation) : Boolean = {
    import walaRes._
    val exec = makeSymbolicExecutor(walaRes)    
    // TODO: extract a relevance relation that doesn't need a Qry as input so we don't need this
    val heapConstraints = Util.makeSet[HeapPtEdge]
    heapConstraints += witnessMe.asInstanceOf[HeapPtEdge]
    val emptyQry = new Qry(heapConstraints, Util.makeSet[PureConstraint], new CallStack, new Z3Solver)
    val path = new Path(emptyQry)
    var instrNum = 1
    val producers = relRelation.getProducers(witnessMe, emptyQry)
    producers.exists(p => {
      val (node, instr) = p
      print(s"Starting on producer instr $instrNum of " + producers.size + ": "); ClassUtil.pp_instr(instr, node.getIR()); println
      instrNum += 1
      val copy = path.deepCopy
      Path.setupJumpPath(copy, instr, node, hm, hg, walaRes.cha)
      exec.executeBackward(copy.qry)
    })
  } 
  
  override def makeAnalysisScope(addJavaLibs : Boolean = true) : AnalysisScope = {
    super.makeAnalysisScope(!isRegression) // in the regression tests, we use an Android lib that has the Java libraries included
  }
}

object AndroidLeakClientTests extends ClientTests {
    
  override def runRegressionTests() : Unit = {
    Options.MAX_PATH_CONSTRAINT_SIZE = 10
    Options.PRIM_ARRAY_SENSITIVITY = true
  
    val tests = List("IntraproceduralStrongUpdate", "SimpleNoRefute", "FunctionCallRefute",
        "FunctionCallNoRefute", "BranchRefute", "BranchNoRefute", "HeapRefute", "HeapNoRefute", "InterproceduralRefute",
        "PathValueUpdateRefute", "PathValueUpdateNoRefute", "SharedStaticMapNoRefute", "ManuNoRefute2", "MultiWayBranchNoRefute",
        "MultiWayBranchRefute", "SubBranchRefute", "MultiBranchUpdateRefute", "IrrelevantLoopRefute", "IrrelevantLoopNoRefute",
        "MultiBranchAndThrowNoRefute", "SimpleDynamicDispatchRefute", "SimpleDynamicDispatchNoRefute", "ReturnValueNoRefute",
        "ReturnValueRefute", "BranchInLoopNoRefute", "BranchInLoopRefute", "DoubleLoopNoRefute", "DoubleLoopRefute",
        "LoopInBranchRefute", "LoopInBranchNoRefute", "HeapReturnRefute", "HeapReturnNoRefute", "NullRefute",
        "NullNoRefute", "IrrelevantBranchNoRefute", "UninitVarRefute", "UninitVarNoRefute", "ArrayLengthRefute",
        "ArrayLengthNoRefute", "DoubleLoopAndBranchNoRefute", 
        //"SimpleDisjunctiveRefute", // broken with stack overflow right now 
        "SimpleDisjunctiveNoRefute", "HarderDisjunctiveRefute", "BranchReturnRefute",
        "SimpleConjunctiveRefute", "SimpleConjunctiveNoRefute", "MultiLevelParamPassRefute", "MultiLevelParamPassNoRefute",
        "StartInLoopNoRefute", "CallInLoopHeadRefute", "CallInLoopHeadNoRefute", "LoopProcRefute", "LoopProcNoRefute", "BreakLoopNoRefute",
        "ForEachLoopRefute", "ForEachLoopNoRefute",
        //"InfiniteLoopRefute",
        "StraightLineCaseSplitNoRefute", "ManuLoopNoRefute",
        "CallPruningNoRefute", "SingletonNoRefute", "ForEachLoopArrRefute", "CheckCastNoRefute", "BranchReturnRefute",
        "IndexSensitiveRefute", "IndexSensitiveNoRefute", "IndexSensitiveDefaultValRefute", "IndexSensitiveDefaultValNoRefute",
        "IndexSensitiveVarIndexRefute", "IndexSensitiveVarIndexNoRefute", 
        "LoopThrowNoRefute", "DoLoopRefute",
        "SimpleAliasingNoRefute", 
        //"SimpleHashMapRefute", // can't refute currently 
        //"SimpleHashMapNoRefute", 
        "ContainsKeyRefute", "ContainsKeyNoRefute")
  
        // TODO: break, continue, labeled break, labeled continue, do...while
           
      //val tests0 = List("MultiWayBranchNoRefute")
      //val tests0 = List("SimpleDisjunctiveRefute")
      //val tests0 = List("InfiniteLoopRefute")
      //val tests0 = List("ReturnValueNoRefute")
      //val tests0 = List("MultiBranchUpdateRefute")
      //val tests0 = List("PathValueUpdateRefute")
      val tests0 = List("IndexSensitiveRefute")
      //val tests0 = List("ContainsKeyNoRefute")
      val regressionDir = "../thresher/apps/tests/regression/"
      //val regressionDir = "../scwala/test/"
      val mainClass = "LAct"
      var testNum = 0
      var successes = 0
      var failures = 0
      
      val executionTimer = new Timer
      val pwTimeoutOk = List("SimpleHashMapNoRefute")
      
      tests foreach (test => if (Options.TEST == null || Options.TEST.isEmpty() || Options.TEST == test) {
        testNum += 1
        println("Running test " + testNum + ": " + test)
        val mayFail = {
          try {
            val path = regressionDir + test
            Options.INDEX_SENSITIVITY = test.contains("IndexSensitive")
            executionTimer.start
            new AndroidLeakClient(path, Util.strToOption(Options.LIB), mainClass, "main", isRegression = true).checkAnnotations          
          } catch {
            case e : BudgetExceededException =>
              // for piecewise, a timeout is the expected result for some tests
              if (Options.PIECEWISE_EXECUTION && !pwTimeoutOk.contains(test)) true
              else {
                printTestFailureMsg(test, testNum)
                throw e
              }
            case e : Throwable => 
              printTestFailureMsg(test, testNum)
              throw e
          }
        }
        executionTimer.stop
        
        // tests that we aren't meant to refute have NoRefute in name
        val expectedResult = test.contains("NoRefute")
        if (mayFail == expectedResult) {
        //if (mayFail == expectedResult || (!test.contains("NoRefute") && mayFail)) { //hack for testing piecewise
          println("Test " + test + " (# " + testNum + ") passed!")
          successes += 1
        } else {
          printTestFailureMsg(test, testNum)
          failures += 1
          if (Options.EXIT_ON_FAIL) sys.error("Test failure")
        }
        
        println("Test took " + (executionTimer.time).toInt + " seconds.")
        println("Execution time " + executionTimer.time)
        edu.colorado.thresher.core.WALACFGUtil.clearCaches()
        LoopUtil.clearCaches
        executionTimer.clear
      }) 
    }
  }