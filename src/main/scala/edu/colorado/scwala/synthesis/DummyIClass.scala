package edu.colorado.scwala.synthesis

import java.io.InputStream
import scala.collection.JavaConversions._
import com.ibm.wala.classLoader.IClass
import com.ibm.wala.classLoader.IClassLoader
import com.ibm.wala.classLoader.IField
import com.ibm.wala.classLoader.IMethod
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.types.Selector
import com.ibm.wala.types.TypeName
import com.ibm.wala.types.TypeReference
import com.ibm.wala.types.annotations.Annotation
import com.ibm.wala.util.strings.Atom
import edu.colorado.scwala.util.Util
import edu.colorado.scwala.util.ClassUtil

trait DummyIClass extends IClass

object DummyIClass {
  
  /** @return - a dummy subclass of @param toSubclass that has been added to the class hierarchy @param cha */
  def findOrCreateDummySubclass(toSubclass : IClass, cha : IClassHierarchy) : DummyIClass = {
    // TODO: would like to cache, but it is causing problems
    //val dummyClass = dummyImpls.getOrElseUpdate(toSubclass, new DummyIClassImpl(toSubclass, cha))
    val dummyClass = new DummyIClassImpl(toSubclass, cha)
    println("Creating dummyImpl " + dummyClass)

    // IMPORTANT! otherwise lookups of the class will fail. Also, it's important to do this here rather than in DummyClassImpl
    // because if we reuse the dummy impl map across analysis of multiple apps that use the same interface type (as we do in 
    // the regression tests), then we need to be careful that the dummy subclass is always in the class hierarchy for app under analysis
    cha.addClass(dummyClass)
    dummyClass
  }
}

private class DummyIClassImpl(clazz : IClass, cha : IClassHierarchy) extends DummyIClass {        
  require(clazz.isInterface() || clazz.isAbstract()) // for now, only expecting this to be called on interface/abstract classes, though could easily be extended   
  // avoid NPE in the case that clazz lives in default package (WALA returns null for this)
  val pkg = clazz.getName().getPackage()
  val pkgName = if (pkg != null) pkg.toString() else "DUMMY" 
      
  val dummyClassType = TypeReference.findOrCreateClass(clazz.getClassLoader().getReference(), pkgName,
                                                           "DUMMY_" + clazz.getName().getClassName().toString())
                                                           
  val (allMethods, declaredMethods) = clazz.getAllMethods().foldLeft ((List.empty[IMethod], List.empty[IMethod])) ((pair, m) => {
    val (allMethods, declaredMethods) = pair
    if (m.isAbstract()) {
      val newM = new DummyIMethod(m, this, cha)
      (newM :: allMethods, newM :: declaredMethods)
    } else (m :: allMethods, declaredMethods)        
  })

  val methodMap = allMethods.foldLeft (Map.empty[Selector,IMethod]) ((map, m) => map + (m.getSelector() -> m))
  
  cha.addClass(this) 
                                                           
  // meaningful overrides                              
  override def getName() : TypeName = dummyClassType.getName()
  override def getReference() : TypeReference = dummyClassType
  override def isInterface() : Boolean = false
  override def isAbstract() : Boolean = false
  override def getSuperclass() : IClass = clazz
  override def getSourceFileName() : String = null
  override def getSource() = null
  override def getDirectInterfaces() : java.util.Collection[_ <: IClass] = java.util.Collections.singleton(clazz)
  override def getAllImplementedInterfaces : java.util.Collection[IClass] = {
    val l = new java.util.LinkedList(clazz.getAllImplementedInterfaces())
    l.add(clazz)
    l
  }      
  override def getDeclaredMethods() : java.util.Collection[IMethod] = declaredMethods  
  override def getMethod(selector : Selector) : IMethod = methodMap(selector)
  override def getAllMethods() : java.util.Collection[IMethod] = allMethods
      
  // all other methods delegate to superclass      
  override def getClassLoader() : IClassLoader = clazz.getClassLoader()
  override def isPublic() : Boolean = clazz.isPublic()
  override def isPrivate() : Boolean = clazz.isPrivate()     
  override def getModifiers() : Int = clazz.getModifiers()
  override def getField(name : Atom) : IField = clazz.getField(name)   
  override def getField(name : Atom, typ : TypeName) : IField = clazz.getField(name, typ)   
  override def getClassInitializer() : IMethod = clazz.getClassInitializer()
  override def isArrayClass() : Boolean = clazz.isArrayClass()
  
  override def getAllInstanceFields() : java.util.Collection[IField] = clazz.getAllInstanceFields()
  override def getAllStaticFields() : java.util.Collection[IField] = clazz.getAllStaticFields()
  override def getAllFields() : java.util.Collection[IField] = clazz.getAllFields()
  override def getDeclaredInstanceFields() : java.util.Collection[IField] = clazz.getDeclaredInstanceFields()
  override def getDeclaredStaticFields() : java.util.Collection[IField] = clazz.getDeclaredStaticFields()
  override def isReferenceType() : Boolean = clazz.isReferenceType()
  override def getAnnotations() : java.util.Collection[Annotation] = clazz.getAnnotations()
  override def getClassHierarchy() : IClassHierarchy = clazz.getClassHierarchy()
  
  override def toString : String = "DUMMY_" + ClassUtil.pretty(clazz)
}