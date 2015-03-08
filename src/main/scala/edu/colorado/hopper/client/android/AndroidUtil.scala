package edu.colorado.hopper.client.android

import com.ibm.wala.ipa.callgraph.{CallGraph, CGNode}
import com.ibm.wala.util.graph.traverse.BFSIterator
import edu.colorado.walautil.{GraphUtil, ClassUtil}
import scala.collection.JavaConversions._

object AndroidUtil {

  def isEntrypointCallback(n : CGNode, cg : CallGraph) : Boolean =
    !ClassUtil.isLibrary(n) && cg.getPredNodes(n).exists(n => ClassUtil.isLibrary(n))

  // special reachability check to account for call graph imprecision in Android apps. the problem is that whenever a
  // method that places a message on the event queue is reachable, this starts a thread that calls dispatchMessage()
  // and then can pull *any* message off of the event queue (and thus call pretty much anything). we prevent this from
  // happening by cutting off paths that pass through Handler.dispatchMessage()
  def getReachableInAndroidCG(cg : CallGraph, n : CGNode) : Set[CGNode] = {
    val HANDLER_CLASS = "Landroid/os/Handler"
    val DISPATCH_MESSAGE = "dispatchMessage"
    def frontierFilter(n : CGNode) : Boolean = {
      val m = n.getMethod
      m.getDeclaringClass.getName.toString == HANDLER_CLASS && m.getName.toString == DISPATCH_MESSAGE
    }
    val iter =
      new BFSIterator[CGNode](cg, n) {
        override def getConnected(n : CGNode) : java.util.Iterator[_ <: CGNode] =
          cg.getSuccNodes(n).filter(n => frontierFilter(n))
      }
    GraphUtil.bfsIterFold(iter, Set.empty[CGNode], ((s : Set[CGNode], n : CGNode) => s + n))
  }

}
