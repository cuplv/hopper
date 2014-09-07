package edu.colorado.scwala.util

import scala.collection.JavaConversions._
import edu.colorado.scwala.state.PtEdge
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.callgraph.propagation.HeapModel
import edu.colorado.scwala.state.Var
import com.ibm.wala.ipa.callgraph.ContextKey
import edu.colorado.scwala.state.LocalPtEdge
import edu.colorado.scwala.util.Types._
import edu.colorado.scwala.state.ObjVar
import com.ibm.wala.ipa.callgraph.CallGraph
import com.ibm.wala.classLoader.IClass
import com.ibm.wala.classLoader.IMethod
import com.ibm.wala.ipa.callgraph.Context
import com.ibm.wala.ssa.IR
import com.ibm.wala.classLoader.CallSiteReference
import com.ibm.wala.ssa.DefUse
import com.ibm.wala.classLoader.NewSiteReference

object CGNodeUtil {
  
  /** find fakeWorldClinit node (class initializers) */      
  def getFakeWorldClinitNode(cg : CallGraph) : Option[CGNode] = {
    val fakeRoot = cg.getFakeRootNode()
    // if there is a fakeWorldClinit, it is always called by fakeRoot
    fakeRoot.iterateCallSites().find(site => {
      val target = site.getDeclaredTarget()
      target.getDeclaringClass() == fakeRoot.getMethod().getDeclaringClass().getReference() &&
      target.getName().toString() == "fakeWorldClinit"
    }) match {
      case Some(target) => 
        val nodes = cg.getPossibleTargets(fakeRoot, target)
        assert(nodes.size() == 1) // there should only be one fakeWorldClinit!
        Some(nodes.iterator().next())
      case None => None
    }
  }
  /*
  // special CGNode to use as a class init node when WALA fails to generate one
  val FAKE_CLINIT = new CGNode {
    override def getMethod : IMethod = Util.unimp("getMethod")
    override def getContext : Context = Util.unimp("getContext")
    override def addTarget(c : CallSiteReference, target : CGNode) : Boolean = Util.unimp("addTarget")
    override def getIR : IR = Util.unimp("getIR")
    override def getDU : DefUse = Util.unimp("getDU")
    override def iterateNewSites : java.util.Iterator[NewSiteReference] = Util.unimp("iterateNewSites")
    override def iterateCallSites : java.util.Iterator[CallSiteReference] = Util.unimp("iterateCallSites")
    override def getClassHierarchy : com.ibm.wala.ipa.cha.IClassHierarchy = Util.unimp("getClassHierachy")
    override def getGraphNodeId : Int = Util.unimp("getGraphNodeId")
    override def setGraphNodeId(x : Int) : Unit = Util.unimp("setGraphNodeId")
  }*/
  
  // TODO: add support for converting other kinds of contextual constraints
  /** convert contextual constraints from @param n into LocalPtEdge's that Thresher understands */
  def getContextualConstraints(n : CGNode, localConstraints : MSet[LocalPtEdge], hm : HeapModel) : List[LocalPtEdge] = {
    val ctx = n.getContext()
    val RECEIVER_VALUE_NUM = 1

    ctx.get(ContextKey.RECEIVER) match {
      case i : InstanceKey =>
        val receiverLHS = Var.makeLocalVar(RECEIVER_VALUE_NUM, n, hm)
        localConstraints.find(e => e.src == receiverLHS) match {
          case Some(e) => List(e)
          case None => List(PtEdge.make(receiverLHS, ObjVar(Set(i))))
        }        
      case _ => Nil
    }    
  }
   
  def getClassInitializerFor(clazz : IClass, cg : CallGraph) : Option[CGNode] = clazz.getClassInitializer() match {
    case null => None
    case clinit => 
      val clinits = cg.getNodes(clinit.getReference())
      assert(clinits.size == 1)
      Some(clinits.iterator().next())
  }            
  
}
  