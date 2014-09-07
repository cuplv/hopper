package edu.colorado.scwala.util

import com.ibm.wala.util.graph.Graph
import com.ibm.wala.util.graph.traverse.BoundedBFSIterator

object GraphUtil {

  /** @return all nodes reachable in graph @param g from source node @param src in @param k steps or less */
  def kBFS[T](g : Graph[T], src : T, k : Int) : Set[T] = {
    val bfsIter = new BoundedBFSIterator(g, src, k)
    var l = Set.empty[T]
    while (bfsIter.hasNext()) {
      l = l + bfsIter.next()
    }
    l
  }
  
  /** @return true in a node in @param snks is reachable from @params src in @param k steps or less, false otherwise */
  def reachableInKSteps[T](g : Graph[T], src : T, snks : Set[T], k : Int) : Boolean = {
    val bfsIter = new BoundedBFSIterator(g, src, k)
    while (bfsIter.hasNext()) {
      if (snks.contains(bfsIter.next())) return true
    }
    false
  }
  
}