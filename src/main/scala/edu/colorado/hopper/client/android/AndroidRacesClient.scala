package edu.colorado.hopper.client.android

import java.io.File

import com.ibm.wala.classLoader.IClass
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.callgraph.propagation.HeapModel
import com.ibm.wala.ssa.{SSAInstruction, SSAFieldAccessInstruction, SSAInvokeInstruction}
import edu.colorado.hopper.client.NullDereferenceTransferFunctions
import edu.colorado.hopper.executor.DefaultSymbolicExecutor
import edu.colorado.hopper.piecewise.{DefaultPiecewiseSymbolicExecutor, RelevanceRelation}
import edu.colorado.hopper.state.{Var, PtEdge, Qry, Pure}
import edu.colorado.thresher.core.Options
import edu.colorado.walautil.{IRUtil, ClassUtil}

import scala.collection.JavaConversions._

class AndroidRacesClient(appPath : String, androidLib : File) extends DroidelClient(appPath, androidLib) {

  lazy val tf = new NullDereferenceTransferFunctions(walaRes)
  lazy val exec =
    if (Options.PIECEWISE_EXECUTION) new DefaultPiecewiseSymbolicExecutor(tf, new RelevanceRelation(tf.cg, tf.hg, tf.hm, tf.cha))
    else new DefaultSymbolicExecutor(tf)

  /* @return true if @param i can perform a null dereference */
  def canDerefFail(i : SSAInstruction, n : CGNode, hm : HeapModel, count : Int) = {
    val ir = n.getIR()
    val srcLine = IRUtil.getSourceLine(i, ir)
    print(s"Checking possible null deref #$count "); ClassUtil.pp_instr(i, ir); println(s" at source line $srcLine of ${ClassUtil.pretty(n)}")
    // create the query
    val lpk = Var.makeLPK(i.getUse(0), n, hm)
    val nullPure = Pure.makePureVar(lpk)
    val locEdge = PtEdge.make(lpk, nullPure)
    val qry = Qry.make(List(locEdge), i, n, hm, startBeforeI = true)
    qry.addPureConstraint(Pure.makeEqNullConstraint(nullPure))
    // invoke Thresher and check it
    val foundWitness =
      try {
        exec.executeBackward(qry)
      } catch {
        case e : Throwable =>
          println(s"Error: $e \n${e.getStackTraceString}")
          if (Options.SCALA_DEBUG) throw e
          else true // soundly assume we got a witness
      }
    print(s"Deref #$count "); ClassUtil.pp_instr(i, ir); println(s" at source line $srcLine of ${ClassUtil.pretty(n)} can fail? $foundWitness")
    foundWitness
  }

  def checkForRacingDerefs() = {
    import walaRes._

    val callbackClasses =
      appTransformer.getCallbackClasses().foldLeft (Set.empty[IClass]) ((s, t) => cha.lookupClass(t) match {
        case null => s
        case clazz => s + clazz
      })

    // TODO: check callees of callbacks as well
    def isCallback(n : CGNode) = {
      val declClass = n.getMethod.getDeclaringClass
      callbackClasses.exists(c => cha.isSubclassOf(declClass, c) || cha.implementsInterface(declClass, c))
    }

    val nullDerefs =
      walaRes.cg.foldLeft (0) ((count, n) =>
        if (!ClassUtil.isLibrary(n) && isCallback(n)) n.getIR match {
          case null => count
          case ir =>
            // TODO: can we easily filter out cases where the receiver is the special inner class this var (this$0 etc.)?
            println("Proc is " + ClassUtil.pretty(n))
            val shouldCheck = n.getMethod.getName.toString == "onItemClick"
            ir.getInstructions.foldLeft (count) ((count, i) => i match {
              case i : SSAInvokeInstruction if !i.isStatic && !IRUtil.isThisVar(i.getReceiver) &&
                                               !i.getDeclaredTarget.isInit =>
                if (shouldCheck) canDerefFail(i, n, hm, count)
                count + 1
              case i : SSAFieldAccessInstruction if !i.isStatic && !IRUtil.isThisVar(i.getRef) =>
                if (shouldCheck) canDerefFail(i, n, hm, count)
                count + 1
              case _ => count
            })
        } else count
      )

    println("Found " + nullDerefs + " null derefs")
  }
}
