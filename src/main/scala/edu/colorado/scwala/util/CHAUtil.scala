package edu.colorado.scwala.util

import scala.collection.JavaConversions._
import com.ibm.wala.classLoader.IMethod
import com.ibm.wala.classLoader.IClass
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.types.TypeReference

object CHAUtil {     
  
  /** t1 <: t0? that is, is t1 a subtype of t0? Wrapper of the WALA method that handles Void type correctly */
  def isAssignableFrom(t0 : TypeReference, t1 : TypeReference, cha : IClassHierarchy) : Boolean = (t0, t1) match {
    case (TypeReference.Void, _) =>   
      t1 == TypeReference.Void // only Void is a subtype of Void
    case (_, TypeReference.Void) =>
      // Void is a subtype of Object and itself, but not of anything else
      t0 == TypeReference.Void || t0 == TypeReference.JavaLangObject
    case _ =>          
      val (c0, c1) = (cha.lookupClass(t0), cha.lookupClass(t1))
      c0 != null && c1 != null && cha.isAssignableFrom(c0, c1)
  }
  
  /** @return true if method @param m may override a method in class @param c, false otherwise */
  // this is complicated because covariance in return type is allowed (for all methods), and covariance in parameter types
  // may occur due to the way that generic methods are represented in the bytecode. since we don't have generics in the bytecode,
  // it's not always possible do determine if one method definitely overrides another. we err on the side of reporting overides
  def mayOverride(method : IMethod, c : IClass, cha : IClassHierarchy) : Boolean = c.getDeclaredMethods().exists(m => 
    m.getSelector() == method.getSelector() || 
      (m.getName() == method.getName() && m.getNumberOfParameters() == method.getNumberOfParameters() && 
      isAssignableFrom(m.getReturnType(), method.getReturnType(), cha) && // check that return types are covariant
        // check that parameter types are covariant
        (0 to m.getNumberOfParameters() - 1).forall(i => isAssignableFrom(m.getParameterType(i), method.getParameterType(i), cha)) 
      )
  )
  
  /** @return the superclasses of @param method's declaring class that are highest in the class hierarchy 
   *  and implement @param method. returns an Iterable rather than a single class because a class can implement multiple
   *  interfaces requiring the same method */
  def getOriginalDeclarers(method : IMethod, cha : IClassHierarchy) : Iterable[IClass] = {
    val declClass = method.getDeclaringClass()
    require(declClass.getDeclaredMethods().contains(method))  
    
    // get interfaces declaring method
    val declInterfaces = declClass.getAllImplementedInterfaces().toSet.filter(i => mayOverride(method, i, cha))
    
    // find superclass highest in the type hierarchy declaring method. need to do this in addition to the interface
    // check because a class can implement multiple interfaces (or implement an interface and extend a class)
    @annotation.tailrec
    def getLastDeclarerRec(cur : IClass, last : IClass) : IClass =
      if (!mayOverride(method, cur, cha)) last
      else if (cur.getSuperclass() == null) cur // cur is java.lang.Object            
      else getLastDeclarerRec(cur.getSuperclass(), cur)
      
    // important to use a set here because the last declarer may be an interface
    declInterfaces + getLastDeclarerRec(declClass.getSuperclass(), declClass)
  }   
  
  /** wrapper around normal class hierarchy lookup that crashes with error message on failure*/
  def lookupClass(t : TypeReference, cha : IClassHierarchy) : IClass = cha.lookupClass(t) match {
    case null => sys.error(s"Warning: lookup of type $t failed")
    case clazz => clazz
  }  

}