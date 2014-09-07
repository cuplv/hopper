package edu.colorado.scwala.solver

import edu.colorado.scwala.state.PureVal
import edu.colorado.scwala.state.PureVar

/**
 * A solver which is capable of returning a satisfying assignment
 */
trait ModelSolver[AST] extends Solver[AST] {
  def model: Option[Map[PureVar, PureVal]]
}