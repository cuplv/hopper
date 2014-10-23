package edu.colorado.thresher.core;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.Context;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.cfa.CallerSiteContext;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ContainerContextSelector;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXInstanceKeys;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.types.MethodReference;

public class ImprovedContainerContextSelector extends ContainerContextSelector {

  public ImprovedContainerContextSelector(IClassHierarchy cha, ZeroXInstanceKeys delegate) {
    super(cha, delegate);
  }

  // identify accessor methods emitted by compiler for inner classes to read fields of parent classes. we want to treat
  // these context sensitively
  public static boolean isAccessMethod(MethodReference m) {
    return m.getName().toString().startsWith("access$");
  }

  @Override
  public boolean mayUnderstand(CGNode caller, CallSiteReference site, IMethod targetMethod, InstanceKey receiver) {
    return isAccessMethod(targetMethod.getReference()) || super.mayUnderstand(caller, site, targetMethod, receiver);
  }

  @Override
  public Context getCalleeTarget(CGNode caller, CallSiteReference site, IMethod callee, InstanceKey[] keys) {
    if (isAccessMethod( callee.getReference())) return new CallerSiteContext(caller, site);
    return super.getCalleeTarget(caller, site, callee, keys);
  }

  private final String[] CONTAINER_KEYWORDS_ARR =
    new String[] { "collection", "linkedlist", "arraylist", "stack", "queue", "hashmap", "hashtable" };

  // hack to detect custom collections that don't extend java.util.Collection
  private final boolean hasContainerKeywordInName(IClass c) {
    String className = c.getName().toString().toLowerCase();
    for (String keyword : CONTAINER_KEYWORDS_ARR) {
      if (className.contains(keyword)) return true;
    }
    return false;
  }

  @Override
  public boolean isContainer(IClass c) {
   return super.isContainer(c) || hasContainerKeywordInName(c);
  }

}
