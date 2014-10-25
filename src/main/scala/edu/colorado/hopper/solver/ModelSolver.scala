package edu.colorado.hopper.solver

import edu.colorado.hopper.state.PureVal
import edu.colorado.hopper.state.PureVar

/**
 * A solver which is capable of returning a satisfying assignment
 */
trait ModelSolver[AST] extends Solver[AST] {
  def model: Option[Map[PureVar, PureVal]]
}