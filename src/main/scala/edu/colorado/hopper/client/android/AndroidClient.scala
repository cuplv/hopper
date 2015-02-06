package edu.colorado.hopper.client.android

import java.io.File
import java.util.jar.JarFile

import com.ibm.wala.classLoader.{IClass, IMethod}
import com.ibm.wala.ipa.callgraph.{AnalysisCache, AnalysisOptions, AnalysisScope, CallGraphBuilder}
import com.ibm.wala.ipa.cha.IClassHierarchy
import edu.colorado.hopper.client.Client
import edu.colorado.thresher.core.{FakeMapContextSelector, Options}

abstract class AndroidClient(appPath : String, androidJar : File, libPath : Option[String], mainClass : String,
                             mainMethod : String, isRegression : Boolean = false)
  extends Client(appPath, libPath, mainClass, mainMethod, isRegression) {
  
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
    // add Java libraries unless we are running the regression tests (since we use a Jar that has its own Java library
    // implementation)
    val analysisScope = super.makeAnalysisScope(isRegression || addJavaLibs)
    // add Android libraries
    assert(androidJar.exists(), s"Couldn't find Android JAR file $androidJar")
    analysisScope.addToScope(analysisScope.getPrimordialLoader(), new JarFile(androidJar))
    analysisScope
  }
  
  override def makeCallGraphBuilder(options : AnalysisOptions, cache : AnalysisCache, cha : IClassHierarchy, 
                           analysisScope : AnalysisScope, isRegression : Boolean) : CallGraphBuilder =                           
    if (isRegression) FakeMapContextSelector.makeZeroOneFakeMapCFABuilder(options, cache, cha, analysisScope)
    else super.makeCallGraphBuilder(options, cache, cha, analysisScope, isRegression)
  
}