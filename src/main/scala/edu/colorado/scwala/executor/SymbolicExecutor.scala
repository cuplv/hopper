package edu.colorado.scwala.executor

import edu.colorado.scwala.state.Qry
import edu.colorado.scwala.state.Path

trait SymbolicExecutor {
  def executeBackward(qry : Qry, test : Option[Path => Boolean]) : Iterable[Path]
  /** @return false if the query is refuted, true if the query is may-witnessed*/
  def executeBackward(qry : Qry) : Boolean
  def cleanup() : Unit
}
