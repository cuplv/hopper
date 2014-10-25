package edu.colorado.hopper.client.android

import edu.colorado.hopper.client.Client
import com.ibm.wala.ipa.callgraph.AnalysisCache
import edu.colorado.thresher.core.FakeMapContextSelector
import com.ibm.wala.ipa.callgraph.CallGraphBuilder
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ipa.callgraph.AnalysisOptions
import com.ibm.wala.ipa.callgraph.AnalysisScope
import java.util.jar.JarFile
import edu.colorado.thresher.core.Options
import java.io.File
import com.ibm.wala.classLoader.IMethod
import com.ibm.wala.types.MethodReference
import com.ibm.wala.classLoader.IClass
import com.ibm.wala.ipa.callgraph.ContextSelector
import com.ibm.wala.ipa.callgraph.propagation.SSAContextInterpreter

abstract class AndroidClient(appPath : String, libPath : Option[String], mainClass : String, mainMethod : String, 
    isRegression : Boolean = false) extends Client(appPath, libPath, mainClass, mainMethod, isRegression) {
  
  // TODO: this is a hack. need complete list of methods. can also check is method is override
  def isAndroidFrameworkCallback(m : IMethod, cha : IClassHierarchy) : Boolean = (m.isPublic() || m.isProtected()) && {
    val name = m.getName().toString()
    name.startsWith("on") || name.startsWith("surface")
  }  
  
  // ignore mainClass name for Android clients
  override def isEntrypointClass(c : IClass, analysisScope : AnalysisScope, mainClass : String) : Boolean = 
    analysisScope.isApplicationLoader(c.getClassLoader())
  
  override def isEntrypoint(m : IMethod, cha : IClassHierarchy, mainMethod : String) : Boolean =
    super.isEntrypoint(m, cha, mainMethod) || isAndroidFrameworkCallback(m, cha)
  
  // load Android libraries/our stubs addition to the normal analysis scope loading 
  override def makeAnalysisScope(addJavaLibs : Boolean = true) : AnalysisScope = {
    // add Java libraries unless we are running the regression tests (since we use a Jar that has its own Java library implementation)
    val analysisScope = super.makeAnalysisScope(isRegression || addJavaLibs)
    // add Android libraries 
    val androidJar = if (!new File(Options.ANDROID_JAR).exists()) "../thresher/android/android-2.3_annotated.jar" else Options.ANDROID_JAR      
    analysisScope.addToScope(analysisScope.getPrimordialLoader(), new JarFile(androidJar))
    analysisScope
  }
  
  override def makeCallGraphBuilder(options : AnalysisOptions, cache : AnalysisCache, cha : IClassHierarchy, 
                           analysisScope : AnalysisScope, isRegression : Boolean) : CallGraphBuilder =                           
    if (isRegression) FakeMapContextSelector.makeZeroOneFakeMapCFABuilder(options, cache, cha, analysisScope)
    else super.makeCallGraphBuilder(options, cache, cha, analysisScope, isRegression)
  
}