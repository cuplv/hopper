package edu.colorado.scwala.synthesis

import edu.colorado.scwala.state.PtEdge
import edu.colorado.scwala.state.PureConstraint
import edu.colorado.scwala.solver.ModelSolver
import com.ibm.wala.classLoader.IMethod

trait Synthesizer[A] {
  def synthesize[E](solver: ModelSolver[E],
                    testName: String,
                    entryPoint: IMethod,
                    edges: Iterable[PtEdge],
                    constraints: Iterable[PureConstraint]): A
}