package edu.colorado.hopper.client.android

import java.io.File
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ssa.{SSAInstruction, SSAInvokeInstruction}
import edu.colorado.hopper.state._
import edu.colorado.thresher.core.Options
import scala.collection.JavaConversions._

class AndroidConstantFlowClient(appPath : String,
                                androidLib : File,
                                alarms : List[(Int,Int,Int)], // elements are (iindex,nodeID,bugType)
                                useJPhantom : Boolean = false)
                               extends DroidelClient[Unit](appPath, androidLib, useJPhantom){
  lazy val exec = makeSymbolicExecutor(walaRes)

  def check : Unit = {
    Options.JUMPING_EXECUTION = true
    Options.PRINT_REFS = true
    alarms.foreach{
      case (iindex, nodeID, 1) => (checkBug1 _).tupled(getAlarmSite(iindex,nodeID))
      case (iindex, nodeID, 2) => (checkBug2 _).tupled(getAlarmSite(iindex,nodeID))
      case (iindex, nodeID, 3) => (checkBug3 _).tupled(getAlarmSite(iindex,nodeID))
      case (iindex, nodeID, 4) => (checkBug4 _).tupled(getAlarmSite(iindex,nodeID))
      case (iindex, nodeID, 5) => (checkBug5 _).tupled(getAlarmSite(iindex,nodeID))
      case (iindex, nodeID, 6) => (checkBug6 _).tupled(getAlarmSite(iindex,nodeID))
    }
  }

  private def checkBug1(node : CGNode, i : SSAInstruction) : Unit = {
    require(i.isInstanceOf[SSAInvokeInstruction])
    val instr = i.asInstanceOf[SSAInvokeInstruction]
    require(instr.getDeclaredTarget.getName.toString == "getInstance" && instr.getDeclaredTarget.getDeclaringClass.getName.getClassName.toString == "Cipher")
    println(s"__MUSE_CONSTANT_SEARCH__ Checking alarm {iindex : ${instr.iindex}, nodeID : ${node.getGraphNodeId}, bugType : 1}")
    val encryption_mode = instr.getUse(0)
    if (node.getIR.getSymbolTable.isStringConstant(encryption_mode))
      println(s"__MUSE_CONSTANT_SEARCH__ Constant found : ${node.getIR.getSymbolTable.getStringValue(encryption_mode)}")
    else {
      val enc_mode_lpk = Var.makeLPK(encryption_mode, node, walaRes.hm)
      val enc_mode_pure = Pure.makePureVar(enc_mode_lpk)
      val qry = Qry.make(List(PtEdge.make(enc_mode_lpk, enc_mode_pure)), instr, node, walaRes.hm)
      qry.addPureConstraint(Pure.makeEqConstraint(enc_mode_pure, new StringVal("__MUSE_CONSTANT_SEARCH__")))
      if (exec.executeBackward(qry)) // ONLY OCCURS IN CASE OF TIMEOUT
        println("__MUSE_CONSTANT_SEARCH__ Search timed out")
      else
        println("__MUSE_CONSTANT_SEARCH__ Search completed")
    }
    println(s"__MUSE_CONSTANT_SEARCH__ Done checking alarm {iindex : ${instr.iindex}, nodeID : ${node.getGraphNodeId}, bugType : 1}")
  }
  private def checkBug2(node : CGNode, i : SSAInstruction) : Unit = {???}
  private def checkBug3(node : CGNode, i : SSAInstruction) : Unit = {???}
  private def checkBug4(node : CGNode, i : SSAInstruction) : Unit = {???}
  private def checkBug5(node : CGNode, i : SSAInstruction) : Unit = {???}
  private def checkBug6(node : CGNode, i : SSAInstruction) : Unit = {???}


  def getAlarmSite(iindex : Int, nodeID : Int) : (CGNode, SSAInstruction) = {
    walaRes.cg.find {_.getGraphNodeId == nodeID}
      .flatMap {node =>
        node.getIR.iterateAllInstructions.find {_.iindex == iindex}
          .map {instr => (node,instr)}
      } match {
        case Some(site) => site
        case None => sys.error(s"Alarm site at iindex $iindex of node $nodeID not witnessed in call graph.")
      }
  }

}
