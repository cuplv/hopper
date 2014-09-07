package edu.colorado.thresher.core;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import com.ibm.wala.classLoader.ArrayClass;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.debug.Assertions;

// this class is a composition of SameReceiverEntryPoint and a sound variation of ArgumentTypeEntrypoint that 
// chooses *all* possible allocation sites that have the same type as a given parameter (rather than just picking one)
public class SharedAllocationEntrypoint extends SameReceiverEntrypoint {

  final static boolean DEBUG = false;
  final private TypeReference[][] paramTypes;
  
  public SharedAllocationEntrypoint(IMethod method, IClassHierarchy cha) {
    super(method, cha);
    paramTypes = makeParameterTypes(method);    
    if (DEBUG) {
      System.out.println("Making entrypoint for " + method);
      for (int i = 0; i < paramTypes.length; i++) {       
        if (paramTypes[i] == null) {
          System.out.println("Null paramType for " + i + " method " + method);
          Assertions.UNREACHABLE();
        } else {
          if (paramTypes[i].length == 0) {
            System.out.println("Param type " + i + " is empty.");
            Assertions.UNREACHABLE();
          }/*
          for (int j = 0; j < paramTypes[i].length; j++) {
            System.out.println("Param type " + i + " is " + paramTypes[i][j]);  
          }*/
        }      
      }
    }
  }
  
  @Override
  public TypeReference[] getParameterTypes(int i) {
    return paramTypes[i];
  }

  /*
   * @see com.ibm.wala.ipa.callgraph.Entrypoint#getNumberOfParameters()
   */
  @Override
  public int getNumberOfParameters() {
    return paramTypes.length;
  }
  
  @Override
  protected TypeReference[][] makeParameterTypes(IMethod method) throws IllegalArgumentException {    
    if (method == null) {
      throw new IllegalArgumentException("method == null");
    }
    IClassHierarchy cha = method.getClassHierarchy();
    TypeReference[][] result = new TypeReference[method.getNumberOfParameters()][];
    for (int i = 0; i < result.length; i++) {
      final TypeReference t = method.getParameterType(i);
      TypeReference[] implementors;
      if (!t.isPrimitiveType()) {
        IClass klass = cha.lookupClass(t);
        if (klass == null) implementors = null;
        else if (!klass.isInterface() && klass.isAbstract()) {
          // yes, I've seen classes that are marked as "abstract interface" :)
          implementors = chooseAllConcreteSubClasses(klass, cha);
        } else if (klass.isInterface()) {
          implementors = chooseAllImplementors(klass, cha);
        } else if (klass.isArrayClass()) {
          ArrayClass arrayKlass = (ArrayClass) klass;
          IClass innermost = arrayKlass.getInnermostElementClass();
          if (innermost != null && innermost.isInterface()) {
            implementors = chooseAllImplementors(innermost, cha);
            int j = 0;
            TypeReference arrType = null;
            for (TypeReference impl : chooseAllImplementors(innermost, cha)) {              
              arrType = TypeReference.findOrCreateArrayOf(impl);
              for (int dim = 1; dim < arrayKlass.getDimensionality(); dim++) {
                arrType = TypeReference.findOrCreateArrayOf(arrType);
              }
            }            
            implementors[j++] = arrType;            
          } else implementors = new TypeReference[] { t };
        } else implementors = new TypeReference[] { t };
      } else implementors = new TypeReference[] { t };

      result[i] = (implementors == null) ? new TypeReference[0] : implementors;
    }
    return result;
  }
  
  protected TypeReference[] chooseAllImplementors(IClass iface, IClassHierarchy cha) {
    Set<IClass> implementors = cha.getImplementors(iface.getReference());
    int i = 0;
    TypeReference[] implementorTypeArr = new TypeReference[implementors.size()];
    for (Iterator<IClass> iter = implementors.iterator(); iter.hasNext();) {
      implementorTypeArr[i++] = iter.next().getReference();
    }
    return implementorTypeArr;
  }

  protected TypeReference[] chooseAllConcreteSubClasses(IClass klass, IClassHierarchy cha) {
    Collection<IClass> subclasses = cha.computeSubClasses(klass.getReference());
    List<TypeReference> subclassTypes = new ArrayList<TypeReference>(subclasses.size());
    for (IClass c : cha.computeSubClasses(klass.getReference())) {
      if (!c.isAbstract()) subclassTypes.add(c.getReference());
    }
    if (subclassTypes.isEmpty()) return null;
    else return subclassTypes.toArray(new TypeReference[0]);    
  }
}
