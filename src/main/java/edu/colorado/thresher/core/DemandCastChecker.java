/**
 * Refinement Analysis Tools is Copyright (c) 2007 The Regents of the
 * University of California (Regents). Provided that this notice and
 * the following two paragraphs are included in any distribution of
 * Refinement Analysis Tools or its derivative work, Regents agrees
 * not to assert any of Regents' copyright rights in Refinement
 * Analysis Tools against recipient for recipient's reproduction,
 * preparation of derivative works, public display, public
 * performance, distribution or sublicensing of Refinement Analysis
 * Tools and derivative works, in source code and object code form.
 * This agreement not to assert does not confer, by implication,
 * estoppel, or otherwise any license or rights in any intellectual
 * property of Regents, including, but not limited to, any patents
 * of Regents or Regents' employees.
 *
 * IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT,
 * INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES,
 * INCLUDING LOST PROFITS, ARISING OUT OF THE USE OF THIS SOFTWARE
 * AND ITS DOCUMENTATION, EVEN IF REGENTS HAS BEEN ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE AND FURTHER DISCLAIMS ANY STATUTORY
 * WARRANTY OF NON-INFRINGEMENT. THE SOFTWARE AND ACCOMPANYING
 * DOCUMENTATION, IF ANY, PROVIDED HEREUNDER IS PROVIDED "AS
 * IS". REGENTS HAS NO OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT,
 * UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 */
package edu.colorado.thresher.core;

import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.demandpa.alg.ContextSensitiveStateMachine;
import com.ibm.wala.demandpa.alg.DemandRefinementPointsTo;
import com.ibm.wala.demandpa.alg.DemandRefinementPointsTo.PointsToResult;
import com.ibm.wala.demandpa.alg.refinepolicy.FieldRefinePolicy;
import com.ibm.wala.demandpa.alg.refinepolicy.ManualFieldPolicy;
import com.ibm.wala.demandpa.alg.refinepolicy.RefinementPolicyFactory;
import com.ibm.wala.demandpa.alg.refinepolicy.TunedRefinementPolicy;
import com.ibm.wala.demandpa.alg.statemachine.StateMachineFactory;
import com.ibm.wala.demandpa.flowgraph.IFlowLabel;
import com.ibm.wala.demandpa.util.MemoryAccessMap;
import com.ibm.wala.demandpa.util.PABasedMemoryAccessMap;
import com.ibm.wala.ipa.callgraph.*;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.HeapModel;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
import com.ibm.wala.ipa.callgraph.propagation.PointerKey;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSACheckCastInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.NullProgressMonitor;
import com.ibm.wala.util.Predicate;
import com.ibm.wala.util.ProgressMaster;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.intset.OrdinalSet;

import java.io.IOException;
import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

/**
 * Uses a demand-driven points-to analysis to check the safety of downcasts.
 *
 * @author Manu Sridharan
 *
 * Note -- this is adapted from Manu's original demand cast checker
 */
public class DemandCastChecker {
  public static Pair<DemandRefinementPointsTo,PointerAnalysis> makeDemandPointerAnalysis(AnalysisScope scope,
                                                                                         ClassHierarchy cha,
                                                                                         AnalysisOptions options)
    throws ClassHierarchyException, IllegalArgumentException, CancelException, IOException {

    System.err.print("constructing call graph...");
    final Pair<CallGraph, PointerAnalysis> cgAndPA = buildCallGraph(scope, cha, options);
    CallGraph cg = cgAndPA.fst;
    System.err.println("done");
    System.err.println(CallGraphStats.getStats(cg));
    MemoryAccessMap fam = new PABasedMemoryAccessMap(cg, cgAndPA.snd);
    DemandRefinementPointsTo fullDemandPointsTo =
      DemandRefinementPointsTo.makeWithDefaultFlowGraph(cg, heapModel, fam, cha, options, makeStateMachineFactory());
    fullDemandPointsTo.setRefinementPolicyFactory(chooseRefinePolicyFactory(cha));
    return Pair.make(fullDemandPointsTo,cgAndPA.snd);
  }

  // if true, construct up-front call graph cheaply (0-CFA)
  private static final boolean CHEAP_CG = false;

  private static HeapModel heapModel = null;

  /**
   * builds a call graph, and sets the corresponding heap model for analysis
   *
   * @param scope
   * @param cha
   * @param options
   * @return
   * @throws CancelException
   * @throws IllegalArgumentException
   */
  private static Pair<CallGraph, PointerAnalysis> buildCallGraph(AnalysisScope scope, ClassHierarchy cha,
                                                                 AnalysisOptions options)
    throws IllegalArgumentException, CancelException {
    CallGraph retCG = null;
    PointerAnalysis retPA = null;
    final AnalysisCache cache = new AnalysisCache();
    CallGraphBuilder builder;
    if (CHEAP_CG) {
      builder = Util.makeZeroCFABuilder(options, cache, cha, scope);
      // we want vanilla 0-1 CFA, which has one abstract loc per allocation
      heapModel = Util.makeVanillaZeroOneCFABuilder(options, cache, cha, scope);
    } else {
      builder = Util.makeZeroOneContainerCFABuilder(options, cache, cha, scope);
      heapModel = (HeapModel) builder;
    }
    ProgressMaster master = ProgressMaster.make(new NullProgressMonitor(), 360000, false);
    master.beginTask("runSolver", 1);
    try {
      retCG = builder.makeCallGraph(options, master);
      retPA = builder.getPointerAnalysis();
    } catch (CallGraphBuilderCancelException e) {
      System.err.println("TIMED OUT!!");
      retCG = e.getPartialCallGraph();
      retPA = e.getPartialPointerAnalysis();
    }
    return Pair.make(retCG, retPA);
  }

  private static RefinementPolicyFactory chooseRefinePolicyFactory(ClassHierarchy cha) {
      return new TunedRefinementPolicy.Factory(cha);
  }

  private static StateMachineFactory<IFlowLabel> makeStateMachineFactory() {
    return new ContextSensitiveStateMachine.Factory();
  }

  public static Set<String> findFailingCasts(CallGraph cg, PointerAnalysis pa, DemandRefinementPointsTo dmp)
    throws InvalidClassFileException {

    final IClassHierarchy cha = dmp.getClassHierarchy();
    Set<String> failing = HashSetFactory.make();
    Set<Integer> noMoreRefinement = HashSetFactory.make();

    int numSafe = 0, numMightFail = 0, safeViaPointsTo = 0, count = 0;
    outer: for (Iterator<? extends CGNode> nodeIter = cg.iterator(); nodeIter.hasNext();) {
      CGNode node = nodeIter.next();
      MethodReference method = node.getMethod().getReference();
      TypeReference declaringClass = node.getMethod().getReference().getDeclaringClass();
      // skip library classes
      if (declaringClass.getClassLoader().equals(ClassLoaderReference.Primordial)) {
        continue;
      }
      IR ir = node.getIR();
      if (ir == null)
        continue;
      SSAInstruction[] instrs = ir.getInstructions();
      IBytecodeMethod bytecodeMethod = (IBytecodeMethod) node.getMethod();
      for (int i = 0; i < instrs.length; i++) {
        SSAInstruction instruction = instrs[i];
        if (instruction instanceof SSACheckCastInstruction) {
          SSACheckCastInstruction castInstr = (SSACheckCastInstruction) instruction;
          final TypeReference[] declaredResultTypes = castInstr.getDeclaredResultTypes();

          boolean primOnly = true;
          for (TypeReference t : declaredResultTypes) {
            if (! t.isPrimitiveType()) {
              primOnly = false;
            }
          }
          if (primOnly) {
            continue;
          }

          // bytecode index is the only way we can get different points-to analyses to agree on which casts are the same
          int bytecodeIndex = bytecodeMethod.getBytecodeIndex(i);
          String castId = method + ":" + bytecodeIndex;

          System.out.println("Checking cast #" + ++count + " " + castInstr + " in " + node.getMethod() + ", line ?");
          PointerKey castedPk = heapModel.getPointerKeyForLocal(node, castInstr.getUse(0));
          @SuppressWarnings("unchecked")
          OrdinalSet<InstanceKey> pointsToSet = (OrdinalSet<InstanceKey>) pa.getPointsToSet(castedPk);

          Predicate<InstanceKey> castPred = new Predicate<InstanceKey>() {

            @Override
            public boolean test(InstanceKey ik) {
              TypeReference ikTypeRef = ik.getConcreteType().getReference();
              for (TypeReference t : declaredResultTypes) {
                IClass class1 = cha.lookupClass(t), class2 = cha.lookupClass(ikTypeRef);
                if (class1 == null || class2 == null) return true; // (unsoundly) punt
                if (cha.isAssignableFrom(class1, class2)) {
                  return true;
                }
              }
              return false;
            }

          };

          Collection<InstanceKey> collection = OrdinalSet.toCollection(pointsToSet);
          if (com.ibm.wala.util.collections.Util.forAll(collection, castPred)) {
            System.err.println("SAFE VIA POINTER ANALYSIS: " + castInstr + " in " + node.getMethod());
            numSafe++;
            safeViaPointsTo++;
            continue;
          }

          long startTime = System.currentTimeMillis();
          Pair<PointsToResult, Collection<InstanceKey>> queryResult;
          try {
            queryResult = dmp.getPointsTo(castedPk, castPred);
          } catch (Exception e) {
            // treat failures as timeouts
            queryResult = Pair.make(PointsToResult.BUDGETEXCEEDED, null);
          }

          long runningTime = System.currentTimeMillis() - startTime;
          System.err.println("running time: " + runningTime + "ms");
          final FieldRefinePolicy fieldRefinePolicy = dmp.getRefinementPolicy().getFieldRefinePolicy();
          switch (queryResult.fst) {
            case SUCCESS:
              System.err.println("SAFE: " + castInstr + " in " + node.getMethod());
              if (fieldRefinePolicy instanceof ManualFieldPolicy) {
                ManualFieldPolicy hackedFieldPolicy = (ManualFieldPolicy) fieldRefinePolicy;
                System.err.println(hackedFieldPolicy.getHistory());
              }
              System.err.println("TRAVERSED " + dmp.getNumNodesTraversed() + " nodes");
              numSafe++;
              break;
            case NOMOREREFINE:
              if (queryResult.snd != null) {
                System.err.println("MIGHT FAIL: no more refinement possible for " + castInstr + " in " + node.getMethod());
                noMoreRefinement.add(count);
              } else {
                System.err.println("MIGHT FAILs: exceeded budget for " + castInstr + " in " + node.getMethod());
                System.err.println("skipping.");
              }
              failing.add(castId);
              numMightFail++;
              break;
            case BUDGETEXCEEDED:
              System.err.println("MIGHT FAIL: exceeded budget for " + castInstr + " in " + node.getMethod());
              System.err.println("skipping.");
              failing.add(castId);
              numMightFail++;
              break;
            default:
              Assertions.UNREACHABLE();
          }
        }
      }
    }
    System.err.println("TOTAL SAFE: " + numSafe);
    System.err.println("TOTAL SAFE VIA POINTS-TO: " + safeViaPointsTo);
    System.err.println("TOTAL MIGHT FAIL: " + numMightFail);
    System.err.println("TOTAL NO MORE REFINEMENT: " + noMoreRefinement.size());
    return failing;
  }

}
