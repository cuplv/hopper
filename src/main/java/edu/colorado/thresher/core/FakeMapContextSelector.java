package edu.colorado.thresher.core;

import java.io.InputStream;
import java.util.Map;

import com.ibm.wala.classLoader.*;
import com.ibm.wala.ipa.callgraph.*;
import com.ibm.wala.ipa.callgraph.impl.*;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.*;
import com.ibm.wala.ipa.callgraph.propagation.cfa.*;
import com.ibm.wala.ipa.cha.*;
import com.ibm.wala.ipa.summaries.MethodSummary;
import com.ibm.wala.ipa.summaries.XMLMethodSummaryReader;
import com.ibm.wala.types.*;
import com.ibm.wala.util.intset.*;

/** special context-sensitivity policy for test purposes only 
 * 
 * @author sam
 */
public class FakeMapContextSelector implements ContextSelector {

  private final static TypeName FakeMapName = TypeName.string2TypeName("LFakeMap");

  public final static TypeReference FakeMap = TypeReference.findOrCreate(ClassLoaderReference.Application, FakeMapName);

  public FakeMapContextSelector() {}

  public Context getCalleeTarget(CGNode caller, CallSiteReference site, IMethod callee, InstanceKey[] keys) {
    InstanceKey receiver = null;
    if (keys != null && keys.length > 0 && keys[0] != null) {
      receiver = keys[0];
    }
    // if (receiver != null && callee.getReference().equals(FakeMap)) {
    // return new CallerSiteContext(caller, site);
    // } else {
    if (receiver == null) {
      if (site.getDeclaredTarget().getName().toString().contains("findViewBy")) {
        //Util.Print("WARNING: null receiver for site " + site);
      }
      return Everywhere.EVERYWHERE;      
      // Assertions.UNREACHABLE("null receiver for " + site);
    }
    return new ReceiverInstanceContext(receiver);
    // }
  }

  private static final IntSet thisParameter = IntSetUtil.make(new int[] { 0 });

  public IntSet getRelevantParameters(CGNode caller, CallSiteReference site) {
    if (site.isDispatch() || site.getDeclaredTarget().getNumberOfParameters() > 0) {
      return thisParameter;
    } else {
      return EmptyIntSet.instance;
    }
  }
  
  public static SSAPropagationCallGraphBuilder makeZeroOneContainerCFABuilder(AnalysisOptions options, AnalysisCache cache,
      IClassHierarchy cha, AnalysisScope scope) {

    if (options == null) {
      throw new IllegalArgumentException("options is null");
    }
    com.ibm.wala.ipa.callgraph.impl.Util.addDefaultSelectors(options, cha);
    com.ibm.wala.ipa.callgraph.impl.Util.addDefaultBypassLogic(options, scope, com.ibm.wala.ipa.callgraph.impl.Util.class.getClassLoader(), cha);
    ContextSelector appSelector = null;
    SSAContextInterpreter appInterpreter = null;
    
    //options.setSelector(new Main.AndroidMethodTargetSelector(options.getMethodTargetSelector(), summaries, AndroidUIChecker.findMethods));
    options.setSelector(new LenientClassHierarchyClassTargetSelector(cha));
    
    return new ZeroXContainerCFABuilder(cha, options, cache, appSelector, appInterpreter, ZeroXInstanceKeys.ALLOCATIONS 
        | ZeroXInstanceKeys.SMUSH_MANY //| ZeroXInstanceKeys.SMUSH_PRIMITIVE_HOLDERS
        | ZeroXInstanceKeys.SMUSH_STRINGS | ZeroXInstanceKeys.SMUSH_THROWABLES);
  }
  
  
  /**
   * class target selector that allows instantiation of abstract classes (useful for modeling, and
   * especially important for Android) 
   */
  static class LenientClassHierarchyClassTargetSelector extends ClassHierarchyClassTargetSelector {
    private final IClassHierarchy classHierarchy;

    public LenientClassHierarchyClassTargetSelector(IClassHierarchy cha) {
      super(cha);
      this.classHierarchy = cha;
    }
    
    @Override
    public IClass getAllocatedTarget(CGNode caller, NewSiteReference site) {
      if (site == null) {
        throw new IllegalArgumentException("site is null");
      }
      IClass klass = classHierarchy.lookupClass(site.getDeclaredType());
      if (klass == null) {
        return null;
      } else if (klass.isInterface()) {
        return null;      
      } else {
        return klass;
      }
    }
    
  }

  public static SSAPropagationCallGraphBuilder makeZeroOneFakeMapCFABuilder(AnalysisOptions options, AnalysisCache cache,
      IClassHierarchy cha, AnalysisScope scope) {

    if (options == null) {
      throw new IllegalArgumentException("options is null");
    }
    com.ibm.wala.ipa.callgraph.impl.Util.addDefaultSelectors(options, cha);
    com.ibm.wala.ipa.callgraph.impl.Util.addDefaultBypassLogic(options, scope, com.ibm.wala.ipa.callgraph.impl.Util.class.getClassLoader(), cha);
    ContextSelector appSelector = null;
    SSAContextInterpreter appInterpreter = null;

    ZeroXFakeMapCFABuilder builder = new ZeroXFakeMapCFABuilder(cha, options, cache, appSelector, appInterpreter,
        ZeroXInstanceKeys.ALLOCATIONS | ZeroXInstanceKeys.SMUSH_MANY // | ZeroXInstanceKeys.SMUSH_PRIMITIVE_HOLDERS
            | ZeroXInstanceKeys.SMUSH_STRINGS | ZeroXInstanceKeys.SMUSH_THROWABLES);
    return builder;
  }

}
