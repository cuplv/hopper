package edu.colorado.thresher.core;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.classLoader.NewSiteReference;
import com.ibm.wala.ipa.callgraph.*;
import com.ibm.wala.ipa.callgraph.impl.ClassHierarchyClassTargetSelector;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.ReceiverInstanceContext;
import com.ibm.wala.ipa.callgraph.propagation.SSAContextInterpreter;
import com.ibm.wala.ipa.callgraph.propagation.SSAPropagationCallGraphBuilder;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXContainerCFABuilder;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXInstanceKeys;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.TypeName;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.intset.EmptyIntSet;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.IntSetUtil;
import edu.colorado.walautil.JavaUtil;

import java.io.File;

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
    File nativeSpec = JavaUtil.getResourceAsFile("natives.xml", FakeMapContextSelector.class);
    assert nativeSpec.exists();
    com.ibm.wala.ipa.callgraph.impl.Util.setNativeSpec(nativeSpec.getAbsolutePath());
    com.ibm.wala.ipa.callgraph.impl.Util.addDefaultBypassLogic(options, scope, com.ibm.wala.ipa.callgraph.impl.Util.class.getClassLoader(), cha);
    ContextSelector appSelector = null;
    SSAContextInterpreter appInterpreter = null;

    ZeroXFakeMapCFABuilder builder = new ZeroXFakeMapCFABuilder(cha, options, cache, appSelector, appInterpreter,
        ZeroXInstanceKeys.ALLOCATIONS | ZeroXInstanceKeys.SMUSH_MANY // | ZeroXInstanceKeys.SMUSH_PRIMITIVE_HOLDERS
            | ZeroXInstanceKeys.SMUSH_STRINGS | ZeroXInstanceKeys.SMUSH_THROWABLES);
    return builder;
  }

}
