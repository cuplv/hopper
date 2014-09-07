package edu.colorado.thresher.core;

import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.ContextSelector;
import com.ibm.wala.ipa.callgraph.impl.DelegatingContextSelector;
import com.ibm.wala.ipa.callgraph.propagation.SSAContextInterpreter;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXContainerCFABuilder;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXInstanceKeys;
import com.ibm.wala.ipa.cha.IClassHierarchy;

/** the other piece of a special context-sensitivity policy for test purposes only 
 * 
 * @author sam
 */
public class ZeroXFakeMapCFABuilder extends ZeroXContainerCFABuilder { //ZeroXCFABuilder {
  public ZeroXFakeMapCFABuilder(IClassHierarchy cha, AnalysisOptions options, AnalysisCache cache,
      ContextSelector appContextSelector, SSAContextInterpreter appContextInterpreter, int instancePolicy) {
    super(cha, options, cache, appContextSelector, appContextInterpreter, instancePolicy);
    ContextSelector CCS = makeFakeMapContextSelector(cha, (ZeroXInstanceKeys) getInstanceKeys());
    DelegatingContextSelector DCS = new DelegatingContextSelector(CCS, contextSelector);
    setContextSelector(DCS);
  }

  protected ContextSelector makeFakeMapContextSelector(IClassHierarchy cha, ZeroXInstanceKeys keys) {
    return new FakeMapContextSelector();
  }
}
