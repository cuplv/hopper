package edu.colorado.hopper.client.android

import java.io.File
import com.ibm.wala.ssa.SSAInvokeInstruction
import edu.colorado.hopper.state._
import edu.colorado.thresher.core.Options
import scala.collection.JavaConversions._

class AndroidConstantFlowClient(appPath : String, androidLib : File, useJPhantom : Boolean= false) extends DroidelClient[Unit](appPath, androidLib, useJPhantom){
  def check = {
    Options.JUMPING_EXECUTION = true
    Options.PRINT_REFS = true
    val exec = makeSymbolicExecutor(walaRes)
    this.walaRes.cg.filter{node => node.getIR != null}.foreach{node =>
      node.getIR.iterateAllInstructions().foreach {
        case i : SSAInvokeInstruction if
          i.getDeclaredTarget.getName.toString == "getInstance" && i.getDeclaredTarget.getDeclaringClass.getName.getClassName.toString == "Cipher"
               =>
          println(s"__MUSE_CONSTANT_SEARCH__ Checking instruction [$i]")
          val encryption_mode = i.getUse(0)
          if(node.getIR.getSymbolTable.isStringConstant(encryption_mode))
            println(s"__MUSE_CONSTANT_SEARCH__ Constant found : ${node.getIR.getSymbolTable.getStringValue(encryption_mode)}")
          else{
            val enc_mode_lpk  = Var.makeLPK(encryption_mode,node,walaRes.hm)
            val enc_mode_pure = Pure.makePureVar(enc_mode_lpk)
            val qry = Qry.make(List(PtEdge.make(enc_mode_lpk, enc_mode_pure)),i,node,walaRes.hm)
            qry.addPureConstraint(Pure.makeEqConstraint(enc_mode_pure, new StringVal("__MUSE_CONSTANT_SEARCH__")))
            exec.executeBackward(qry)
          }
        case _ => /* NO OP */
      }

    }
  }

}
