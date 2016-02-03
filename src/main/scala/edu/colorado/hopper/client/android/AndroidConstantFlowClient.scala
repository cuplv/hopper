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
  private def checkBug2(node : CGNode, i : SSAInvokeInstruction) : Unit = {
    require(i.getDeclaredTarget.getName.toString == "init" && i.getDeclaredTarget.getDeclaringClass.getName.getClassName.toString.contains("Cipher"))
    //NOTE(benno) this bug type from the hackathon was specified incorrectly in our document
    // It requires constraints:
    //  - on the non-primitive/non-built-into-java type of an argument to the invocation site
    //  - that the first argument be from a static field
    // These would require significant Hopper extensions, so I'm punting on them.
  }
  private def checkBug3(node : CGNode, i : SSAInvokeInstruction) : Unit = {
    require(i.getDeclaredTarget.getName.toString.contains("<init>") && i.getDeclaredTarget.getDeclaringClass.getName.getClassName.toString.contains("SecretKeySpec"))
    //TODO(benno) need apps to run on....
  }
  private def checkBug4(node : CGNode, i : SSAInvokeInstruction) : Unit = {???}

  private def checkBug5(node : CGNode, i : SSAInvokeInstruction) : Unit = {
    require(i.getDeclaredTarget.getName.toString.contains("<init>") && i.getDeclaredTarget.getDeclaringClass.getName.getClassName.toString.contains("PBE"))
    val iter = i.getUse(2)
    val iter_lpk = Var.makeLPK(iter,node,walaRes.hm)
    val iter_pure = Pure.makePureVar(iter_lpk)
    val qry = Qry.make(List(PtEdge.make(iter_lpk,iter_pure)),i,node,walaRes.hm)
    qry.addPureConstraint(Pure.makeLtConstraint(iter_pure,new IntVal(1000)))
    if (exec.executeBackward(qry)){
      println("__MUSE_CONSTANT_SEARCH__ Bug 5 witnessed")
    } else {
      println("__MUSE_CONSTANT_SEARCH__ Bug 5 refuted")
    }

  }
  private def checkBug6(node : CGNode, i : SSAInvokeInstruction) : Unit = {
    require((i.getDeclaredTarget.getName.toString.contains("<init>") &&
             i.getDeclaredTarget.getDeclaringClass.getName.getClassName.toString == "SecureRandom")
            ||
            (i.getDeclaredTarget.getName.toString.contains("SecureRandom") &&
             i.getDeclaredTarget.getDeclaringClass.getName.getClassName.toString == "setSeed"))
    val arg = i.getUse(0)
    val arg_lpk = Var.makeLPK(arg,node,walaRes.hm)
    val arg_pure = Pure.makePureVar(arg_lpk)
    val qry = Qry.make(List(PtEdge.make(arg_lpk,arg_pure)),i,node,walaRes.hm)
    qry.addPureConstraint(Pure.makeEqConstraint(arg_pure,new ByteArrayVal(null)))
    if (exec.executeBackward(qry)) // Only occurs in case of (1) timeout or (2) hopper soundly dropping difficult constraints
      println("__MUSE_CONSTANT_SEARCH__ Search incomplete")
    else
      println("__MUSE_CONSTANT_SEARCH__ Search complete")
  }


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
