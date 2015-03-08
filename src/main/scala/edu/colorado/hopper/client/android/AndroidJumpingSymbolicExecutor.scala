package edu.colorado.hopper.client.android

import com.ibm.wala.ssa.{IR, ISSABasicBlock}
import edu.colorado.hopper.executor.TransferFunctions
import edu.colorado.hopper.jumping.{DefaultJumpingSymbolicExecutor, RelevanceRelation}
import edu.colorado.hopper.state._
import edu.colorado.thresher.core.Options
import edu.colorado.walautil.ClassUtil

class AndroidJumpingSymbolicExecutor(tf : TransferFunctions, rr : RelevanceRelation)
  extends DefaultJumpingSymbolicExecutor(tf, rr) {

  val DEBUG = Options.SCALA_DEBUG
  // keep guards from loop conditionals. more precise, but potentially costly
  override val keepLoopConstraints = true

  def doJump(p : Path) : Iterable[Path] = {
    require(!p.node.getMethod.isInit)
    if (DEBUG) println(s"After weakening, query is ${p.qry}")
    val curJmp = { jmpNum += 1; jmpNum }

    rr.getPiecewisePaths(p, curJmp) match {
      case Some(unfilteredPiecewisePaths) =>
        val piecewisePaths =
          unfilteredPiecewisePaths.filter(p => !piecewiseInvMap.pathEntailsInv((p.node, p.blk, p.index), p))
        if (DEBUG) {
          println(s"got ${piecewisePaths.size} piecewise paths:")
          piecewisePaths.foreach(p => print(s"\n${p.id}X : ${ClassUtil.pretty(p.node)}\n$p")); println
        }
        piecewisePaths
      case None => super.returnFromCallNoJump(p) // relevance relation decided not to jump
    }
  }

  // choose to jump when we hit an entrypoint callback invoked by the Android framework
  override def returnFromCall(p : Path) : Iterable[Path] =
    if (p.callStack.size == 1 && AndroidUtil.isEntrypointCallback(p.node, cg)) doJump(p)
    else super.returnFromCallNoJump(p)

  // overriding this stops all jumping performed by the superclass, which tries to jump after every instruction. we do
  // this because we only want to consider jumps at function boundaries
  override def forkToPredecessorBlocks(instrPaths : List[Path], startBlk : ISSABasicBlock,
                                       loopHeader : Option[ISSABasicBlock], ir : IR, passPaths : List[Path],
                                       failPaths : List[Path], test : Path => Boolean) =
    super.forkToPredecessorBlocksNoJump(instrPaths, startBlk, loopHeader, ir, passPaths, failPaths, test)

}
