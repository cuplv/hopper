package edu.colorado.hopper.client.android

import java.io.File

import com.ibm.wala.classLoader.IClass
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ssa.{SSAFieldAccessInstruction, SSAInvokeInstruction}
import edu.colorado.walautil.{IRUtil, ClassUtil}

import scala.collection.JavaConversions._


class AndroidRacesClient(appPath : String, androidLib : File) extends DroidelClient(appPath, androidLib) {

  def checkForRacingDerefs() = {
    import walaRes._

    val callbackClasses =
      appTransformer.getCallbackClasses().foldLeft (Set.empty[IClass]) ((s, t) => cha.lookupClass(t) match {
        case null => s
        case clazz => s + clazz
      })

    def isCallback(n : CGNode) = {
      val declClass = n.getMethod.getDeclaringClass
      callbackClasses.exists(c => cha.isSubclassOf(declClass, c) || cha.implementsInterface(declClass, c))
    }

    val nullDerefs =
      walaRes.cg.foldLeft (0) ((count, n) =>
        if (!ClassUtil.isLibrary(n) && isCallback(n)) n.getIR match {
          case null => count
          case ir =>
            println("Proc is " + ClassUtil.pretty(n))
            ir.getInstructions.foldLeft (count) ((count, i) => i match {
              case i : SSAInvokeInstruction if !i.isStatic && !IRUtil.isThisVar(i.getReceiver) &&
                                               !i.getDeclaredTarget.isInit =>
                println("Potential null deref " + i)
                count + 1
              case i : SSAFieldAccessInstruction if !i.isStatic && !IRUtil.isThisVar(i.getRef) =>
                println("Potential null deref " + i)
                count + 1
              case _ => count
            })
        } else count
      )

    println("Found " + nullDerefs + " null derefs")
  }
}
