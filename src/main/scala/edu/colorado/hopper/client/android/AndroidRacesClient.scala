package edu.colorado.hopper.client.android

import java.io.File

import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ssa.{SSAInvokeInstruction, SSAFieldAccessInstruction}
import edu.colorado.hopper.util.ClassUtil
import scala.collection.JavaConversions._


class AndroidRacesClient(appPath : String, androidLib : File) extends DroidelClient(appPath, androidLib) {

  def checkForRacingDerefs() = {
    def isThisVar(useNum : Int) = useNum == 1

    def isCallback(n : CGNode) = {
      // TODO: expose Droidel's callbackClasses list and use this here
      n.getMethod.getName.toString.startsWith("on")
    }

    val nullDerefs =
      walaRes.cg.foldLeft (0) ((count, n) =>
        if (!ClassUtil.isLibrary(n) && isCallback(n)) n.getIR match {
          case null => count
          case ir =>
            println("Proc is " + ClassUtil.pretty(n))
            ir.getInstructions.foldLeft (count) ((count, i) => i match {
              case i : SSAInvokeInstruction if !i.isStatic && !isThisVar(i.getReceiver) && !i.getDeclaredTarget.isInit =>
                println("Potential null deref " + i)
                count + 1
              case i : SSAFieldAccessInstruction if !i.isStatic && !isThisVar(i.getRef) =>
                println("Potential null deref " + i)
                count + 1
              case _ => count
            })
        } else count
      )

    println("Found " + nullDerefs + " null derefs")
  }
}
