package edu.colorado.thresher.core;

import java.util.Map;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.impl.AbstractRootMethod;
import com.ibm.wala.ipa.callgraph.impl.DefaultEntrypoint;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.HashMapFactory;

/**
 * An extension of the DefaultEntrypoint that re-uses receivers of similar types rather than
 * allocating a new receiver for each method call
 * 
 * For example, if we have a class C with methods foo() and bar(), using DefaultEntrypoint's
 * will yield IR:
 * v1 = new C
 * invoke foo v1
 * c2 = new C
 * invoke bar v2
 * 
 * whereas with SameReceiverEntrypoint's, we will get
 * v1 = new C
 * invoke foo v1
 * invoke bar v1
 * 
 * @author sam
 *
 */
public class SameReceiverEntrypoint extends DefaultEntrypoint {
  
  private static final Map<TypeReference,Integer> cachedArgs = HashMapFactory.make();
  public static void clearCachedArgs() { cachedArgs.clear(); }
  private final IClassHierarchy cha;    
  
  public SameReceiverEntrypoint(IMethod method, IClassHierarchy cha) {
    super(method, cha);
    this.cha = cha;
  }

  protected int getOrCreateCachedArg(TypeReference ref, AbstractRootMethod m) {
    if (ref.isPrimitiveType()) return m.addLocal(); // create fresh locals for primitive types
    else {
      Integer result = cachedArgs.get(ref);
      int arg;
      if (result == null) {
        // haven't seen an arg of type ref yet; allocate a new one
        IClass clazz = cha.lookupClass(ref);
        if (clazz == null || clazz.isInterface()) {
          // it's an interface type -- tring to allocated it would be bad
          SSANewInstruction n = m.addAllocation(TypeReference.JavaLangObject);
          arg = m.addCheckcast(new TypeReference[] { ref }, n.getDef(), false);
          cachedArgs.put(ref, arg);
        } else {
          // TODO: calling addAllocation invokes the default constructor for ref, but we may want to try a bit harder and invoke a more interesting one
          SSANewInstruction n = m.addAllocation(ref);
          if (n == null) System.out.println("Failed to add allocation for " + ref);
          arg = n.getDef();
          cachedArgs.put(ref, arg);
        }               
      } else arg = result.intValue();
      return arg;
    }
  }
 
  @Override
  protected int makeArgument(AbstractRootMethod m, int i) {
    TypeReference[] p = getParameterTypes(i);
    if (p.length == 0) return -1;
    else if (p.length == 1) {
      return getOrCreateCachedArg(p[0], m);
    } else {
      int[] values = new int[p.length];
      int countErrors = 0;
      for (int j = 0; j < p.length; j++) {
        int value = getOrCreateCachedArg(p[j], m);
        if (value == -1) {
          countErrors++;
        } else {
          values[j - countErrors] = value;
        }
      }
      if (countErrors > 0) {
        int[] oldValues = values;
        values = new int[oldValues.length - countErrors];
        System.arraycopy(oldValues, 0, values, 0, values.length);
      }   
      return m.addPhi(values);
    }
  }

}
