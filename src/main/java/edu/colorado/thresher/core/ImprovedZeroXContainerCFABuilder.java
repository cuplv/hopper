package edu.colorado.thresher.core;

import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.ContextSelector;
import com.ibm.wala.ipa.callgraph.propagation.SSAContextInterpreter;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXContainerCFABuilder;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXInstanceKeys;
import com.ibm.wala.ipa.cha.IClassHierarchy;

public class ImprovedZeroXContainerCFABuilder extends ZeroXContainerCFABuilder {

  public ImprovedZeroXContainerCFABuilder(IClassHierarchy cha, AnalysisOptions options, AnalysisCache cache,
                                          ContextSelector appContextSelector,
                                          SSAContextInterpreter appContextInterpreter, int instancePolicy) {

    super(cha, options, cache, appContextSelector, appContextInterpreter, instancePolicy);
  }

  @Override
  protected ContextSelector makeContainerContextSelector(IClassHierarchy cha, ZeroXInstanceKeys keys) {
    return new ImprovedContainerContextSelector(cha, keys);
  }
}
