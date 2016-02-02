package edu.colorado.hopper.client.android

import java.io.File
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ssa.SSAInvokeInstruction
import edu.colorado.hopper.state._
import edu.colorado.thresher.core.Options
import edu.colorado.hopper.jumping.JumpingTransferFunctions
import scala.collection.JavaConversions._

class AndroidConstantFlowClient(appPath : String,
                                androidLib : File,
                                alarms : List[(Int,Int,Int)], // elements are (iindex,nodeID,bugType)
                                useJPhantom : Boolean = false)
                               extends DroidelClient[Unit](appPath, androidLib, useJPhantom){
  lazy val exec = {
    val rr = new AndroidRelevanceRelation(appTransformer, walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)
    val tf = new JumpingTransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha, rr)
    new AndroidJumpingSymbolicExecutor(tf,rr)

  }

  def check : Unit = {
    Options.JUMPING_EXECUTION = true
    Options.CONTROL_FEASIBILITY = true
    Options.PRINT_REFS = true
    alarms.foreach { case (iindex,nodeID,bugType) =>
      println(s"__MUSE_CONSTANT_SEARCH__ Checking alarm {iindex : $iindex, cg_node_id : $nodeID, bugType : $bugType}")
      bugType match {
        case 1 => (checkBug1 _).tupled(getAlarmSite(iindex, nodeID))
        case 2 => (checkBug2 _).tupled(getAlarmSite(iindex, nodeID))
        case 3 => (checkBug3 _).tupled(getAlarmSite(iindex, nodeID))
        case 4 => (checkBug4 _).tupled(getAlarmSite(iindex, nodeID))
        case 5 => (checkBug5 _).tupled(getAlarmSite(iindex, nodeID))
        case 6 => (checkBug6 _).tupled(getAlarmSite(iindex, nodeID))
      }
      println(s"__MUSE_CONSTANT_SEARCH__ Done checking alarm {iindex : $iindex, cg_node_id : $nodeID, bugType : $bugType}")
    }
  }

  private def checkBug1(node : CGNode, i : SSAInvokeInstruction) : Unit = {
    require(i.getDeclaredTarget.getName.toString == "getInstance" && i.getDeclaredTarget.getDeclaringClass.getName.getClassName.toString == "Cipher")
    val encryption_mode = i.getUse(0)
    if (node.getIR.getSymbolTable.isStringConstant(encryption_mode)){
      println(s"__MUSE_CONSTANT_SEARCH__ Constant found: {{${node.getIR.getSymbolTable.getStringValue(encryption_mode)}}}")
      println("__MUSE_CONSTANT_SEARCH__ Search complete")
    } else {
      val enc_mode_lpk = Var.makeLPK(encryption_mode, node, walaRes.hm)
      val enc_mode_pure = Pure.makePureVar(enc_mode_lpk)
      val qry = Qry.make(List(PtEdge.make(enc_mode_lpk, enc_mode_pure)), i, node, walaRes.hm)
      qry.addPureConstraint(Pure.makeEqConstraint(enc_mode_pure, new StringVal("__MUSE_CONSTANT_SEARCH__")))
      if (exec.executeBackward(qry)) // Only occurs in case of (1) timeout or (2) hopper soundly dropping difficult constraints
        println("__MUSE_CONSTANT_SEARCH__ Search incomplete")
      else
        println("__MUSE_CONSTANT_SEARCH__ Search complete")
    }
  }
  private def checkBug2(node : CGNode, i : SSAInvokeInstruction) : Unit = {???}
  private def checkBug3(node : CGNode, i : SSAInvokeInstruction) : Unit = {???}
  private def checkBug4(node : CGNode, i : SSAInvokeInstruction) : Unit = {???}
  private def checkBug5(node : CGNode, i : SSAInvokeInstruction) : Unit = {???}
  private def checkBug6(node : CGNode, i : SSAInvokeInstruction) : Unit = {???}


  def getAlarmSite(iindex : Int, nodeID : Int) : (CGNode, SSAInvokeInstruction) = {
    walaRes.cg.find {_.getGraphNodeId == nodeID}
      .flatMap {node =>
        node.getIR.iterateAllInstructions.find {_.iindex == iindex}
          .map {instr =>
            require(instr.isInstanceOf[SSAInvokeInstruction])
            (node,  instr.asInstanceOf[SSAInvokeInstruction])}
      } match {
        case Some(site) => site
        case None => sys.error(s"Alarm site at iindex $iindex of node $nodeID not witnessed in call graph.")
      }
  }

}
