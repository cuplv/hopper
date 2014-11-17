package edu.colorado.hopper.synthesis

import scala.collection.JavaConversions._
import com.ibm.wala.classLoader.IClass
import com.ibm.wala.classLoader.IMethod
import com.ibm.wala.classLoader.NewSiteReference
import com.ibm.wala.classLoader.SyntheticMethod
import com.ibm.wala.ipa.callgraph.Context
import com.ibm.wala.ipa.callgraph.impl.Everywhere
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ipa.summaries.SyntheticIR
import com.ibm.wala.ssa.IR
import com.ibm.wala.ssa.SSAInstruction
import com.ibm.wala.ssa.SSAOptions
import com.ibm.wala.types.Descriptor
import com.ibm.wala.types.MethodReference
import com.ibm.wala.types.Selector
import com.ibm.wala.types.TypeReference
import com.ibm.wala.types.annotations.Annotation
import com.ibm.wala.util.strings.Atom
import edu.colorado.walautil.{IRUtil, CHAUtil}

class DummyIMethod(m : IMethod, c : DummyIClass, cha : IClassHierarchy) extends SyntheticMethod(m.getReference, c, m.isStatic(), false) {
  require(m.isAbstract())        
    
  override def getDeclaringClass() : IClass = c
  // say that we're NOT abstract -- otherwise we won't have an opportunity to inject a stub for the method body
  override def isAbstract() : Boolean = false
  // say that we're native so that no one asks what our body is at this point (we don't know what it should be yet)
  override def isNative() : Boolean = false 
  override def isSynthetic() : Boolean = true

  var dummyIndexCounter = 0
  def getDummyIndex() : Int = {
    dummyIndexCounter += 1
    dummyIndexCounter
  }

  // for a method whose return type is T, generate the dummy IR "return new T()"
  // generate a dummy IR that allocates an instance of the type of the return value of the method and returns it
  // if the return type is a primitive type generate an empty IR
  override def makeIR(ctx : Context, options : SSAOptions) : IR = 
    if (m.getReturnType().isPrimitiveType()) {
      // TODO: return arbitrary primitive type? will this cause exceptions?
      null
    } else {
      val clazz = cha.lookupClass(m.getReturnType())
      val retTypeClass = if (clazz.isInterface() || clazz.isAbstract()) // can't allocate an instance of clazz
        if (clazz == m.getDeclaringClass()) c // clazz is the type that we are already synthesizing a dummy impl for. return our dummy impl
        else DummyIClass.findOrCreateDummySubclass(clazz, cha) // need to synthesize a dummy subclass for clazz
      else clazz // easy case -- we can directly allocate clazz
        
      // get fresh value number for def (make sure not to use one of the param value numbers)
      var freshValueNumCounter = m.getNumberOfParameters()
      def mkFreshValueNum() : Int = { freshValueNumCounter += 1; freshValueNumCounter }
      
      val instrs =
        if (retTypeClass.getReference() == TypeReference.JavaLangObject) {
          // inserted special hack here for Nick. when the return type is Object and we downcast it (for example, if we cast the result of
          // iterator.next() to some non-Object type T via the instruction x = (T) iterator.next(), then the variable x will always be
          // null and will cause all sorts of problems)
          // this is a hack that doesn't solve the problem fully. when the return type is Object here, we return a phi of all possible concrete types
          // a smarter thing to do would be to find all cast instructions and return a phi of all types T involved in downcasts
          val subs = if (retTypeClass.isInterface()) cha.getImplementors(retTypeClass.getReference()) else cha.computeSubClasses(retTypeClass.getReference())
          val concreteSubs = subs.filter(c => !c.isAbstract() && !c.isInterface())
          concreteSubs.foldLeft (List.empty[SSAInstruction]) ((instrs, c) => {
            // allocate an instance whose type is the return value of the method          
            val defNum = mkFreshValueNum// get fresh value number for def (make sure not to use one of the param value numbers)
            val newSite = new NewSiteReference(defNum, c.getReference())
            val newInstr = IRUtil.factory.NewInstruction(getDummyIndex(), defNum, newSite)
            val retInstr = IRUtil.factory.ReturnInstruction(getDummyIndex(), defNum, false)
            newInstr :: retInstr :: instrs
          })
        } else {
          // allocate an instance whose type is the return value of the method
          val newSite = new NewSiteReference(0, retTypeClass.getReference())          
          val newDef = mkFreshValueNum 
          val newInstr = IRUtil.factory.NewInstruction(getDummyIndex(), newDef, newSite)
          val retInstr = IRUtil.factory.ReturnInstruction(getDummyIndex(), newDef, false)
          List(newInstr, retInstr)
        }                
     
      val instrArray = instrs.toArray
      new SyntheticIR(this, Everywhere.EVERYWHERE, makeControlFlowGraph(instrArray), instrArray, options, java.util.Collections.emptyMap())
    }    
      
  override def getAnnotations() : java.util.Collection[Annotation] = m.getAnnotations()
  override def getClassHierarchy() : IClassHierarchy = m.getClassHierarchy()           
  override def getName() : Atom = m.getName() 
  override def isStatic() : Boolean = m.isStatic() 
  override def getDeclaredExceptions() : Array[TypeReference] = m.getDeclaredExceptions() 
  override def getDescriptor() : Descriptor = m.getDescriptor() 
  override def getLineNumber(x$1: Int) : Int = m.getLineNumber(x$1)
  override def getLocalVariableName(x$1: Int,x$2: Int) : String = m.getLocalVariableName(x$1, x$2)
  override def getNumberOfParameters() : Int = m.getNumberOfParameters()
  override def getParameterType(x$1: Int) : TypeReference = m.getParameterType(x$1) 
  override def getReference() : MethodReference = m.getReference() 
  override def getReturnType() : TypeReference = m.getReturnType() 
  override def getSelector() : Selector = m.getSelector() 
  override def getSignature() : String = m.getSignature() 
  override def hasExceptionHandler() : Boolean = m.hasExceptionHandler() 
  override def hasLocalVariableTable() : Boolean = m.hasLocalVariableTable() 
  override def isBridge() : Boolean = m.isBridge() 
  override def isClinit() : Boolean = m.isClinit() 
  override def isFinal() : Boolean = m.isFinal()
  override def isInit() : Boolean = m.isInit() 
  override def isPrivate() : Boolean = m.isPrivate() 
  override def isProtected() : Boolean = m.isProtected() 
  override def isPublic(): Boolean = m.isPublic() 
  override def isSynchronized() : Boolean = m.isSynchronized()
}
