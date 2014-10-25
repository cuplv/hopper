package edu.colorado.hopper.synthesis

import edu.colorado.hopper.state.PtEdge
import edu.colorado.hopper.state.PureConstraint
import edu.colorado.hopper.solver.ModelSolver
import com.ibm.wala.classLoader.IMethod

trait Synthesizer[A] {
  def synthesize[E](solver: ModelSolver[E],
                    testName: String,
                    entryPoint: IMethod,
                    edges: Iterable[PtEdge],
                    constraints: Iterable[PureConstraint]): A
}