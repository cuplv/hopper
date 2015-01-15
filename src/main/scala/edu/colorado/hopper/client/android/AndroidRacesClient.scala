package edu.colorado.hopper.client.android

import java.io.File

import com.ibm.wala.classLoader.{IField, IClass}
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.callgraph.propagation.{StaticFieldKey, InstanceFieldKey, HeapModel}
import com.ibm.wala.ssa._
import edu.colorado.droidel.driver.AbsurdityIdentifier
import edu.colorado.hopper.executor.DefaultSymbolicExecutor
import edu.colorado.hopper.piecewise.{AndroidRelevanceRelation, DefaultPiecewiseSymbolicExecutor, PiecewiseTransferFunctions}
import edu.colorado.hopper.state._
import edu.colorado.hopper.util.PtUtil
import edu.colorado.thresher.core.Options
import edu.colorado.walautil.Types.MSet
import edu.colorado.walautil.{ClassUtil, IRUtil, Util}

import scala.collection.JavaConversions._
import scala.xml.XML

class AndroidRacesClient(appPath : String, androidLib : File) extends DroidelClient(appPath, androidLib) {
  val DEBUG = false
  lazy val rr = new AndroidRelevanceRelation(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)

  // TODO: mixin null deref transfer functions and pw transfer functions, or otherwise allow code reuse
  lazy val tf = new PiecewiseTransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha, rr) {

    /** @return true if we should add the conditional expression from @param cond as a constraint given that we want to
      * refute @param qry, false otherwise */
    def shouldAddConditionalConstraint(cond : SSAConditionalBranchInstruction, qry : Qry, n : CGNode) : Boolean = {
      val tbl = n.getIR().getSymbolTable()
      val queryInstanceKeys = qry.getAllObjVars.flatMap(o => o.rgn)

      def useMayBeRelevantToQuery(use : Int) : Boolean = !tbl.isConstant(use) && {
        val lpk = Var.makeLPK(use, n, hm)
        // the query refers to a local in the query
        qry.localConstraints.exists(e => e.src.key == lpk) || {
          // TODO: this does not capture guards enforcing object invariants, among other things
          // the query points at a heap loc reachable in the heap from the local constraint
          !queryInstanceKeys.intersect(PtUtil.getPt(lpk, hg)).isEmpty || {
            // get the fields that point at the object(s) the local pointer key points at
            val lpkFields =
              hg.getSuccNodes(lpk).foldLeft (Set.empty[IField]) ((s, k) =>
                hg.getPredNodes(k).foldLeft (s) ((s, k) => k match {
                  case k : InstanceFieldKey => s + k.getField
                  case k : StaticFieldKey => s + k.getField
                  case _ => s
                })
              )
            // the query contains a field that may point at the object(s) the local pointer key points at
            !lpkFields.intersect(qry.getAllFields()).isEmpty
          }
        }
      }

      val shouldAdd = useMayBeRelevantToQuery(cond.getUse(0)) || useMayBeRelevantToQuery(cond.getUse(1))
      if (DEBUG && !shouldAdd) {
        print("Not adding cond "); ClassUtil.pp_instr(cond, n.getIR); println(" since it may be irrel")
      }
      shouldAdd
    }

    override def executeCond(cond : SSAConditionalBranchInstruction, qry : Qry, n : CGNode,
                             isThenBranch : Boolean) : Boolean =
      // decide whether or not we should keep the condition
      if (shouldAddConditionalConstraint(cond, qry, n)) super.executeCond(cond, qry, n, isThenBranch)
      else true

    // TODO: refute based on dominating null checks for re-used fields
    override def execute(s : SSAInstruction, qry : Qry, n : CGNode) : List[Qry] = s match {
      case i : SSAGetInstruction if !i.isStatic && ClassUtil.isInnerClassThis(i.getDeclaredField) =>
        PtUtil.getConstraintEdge(Var.makeLPK(i.getDef, n, hm), qry.localConstraints) match {
          case Some(LocalPtEdge(_, p@PureVar(_))) if qry.isNull(p) =>
            // have x == null and x = y.this$0 (or similar). reading from this$0 will never return null without bytecode
            // editor magic (or order of initialization silliness)--refute
            if (Options.PRINT_REFS) println("Refuted by read from inner class this!")
            Nil
          case _ => super.execute(s, qry, n)
        }
      case i : SSAFieldAccessInstruction if !i.isStatic() => // x = y.f or y.f = x
        PtUtil.getConstraintEdge(Var.makeLPK(i.getRef(), n, hm), qry.localConstraints) match {
          case Some(LocalPtEdge(_, p@PureVar(_))) if qry.isNull(p) =>
            // y is null--we could never have reached the current program point because executing this instruction would
            // have thrown a NPE
            if (Options.PRINT_REFS) println("Refuted by dominating null check!")
            Nil
          case _ => super.execute(s, qry, n)
        }
      case i : SSAInvokeInstruction if !i.isStatic() => // x = y.m(...)
        sys.error("This case should be handled in SymbolicExcutor.executeInstr")
      case _ => super.execute(s, qry, n)
    }

    private val nonNullRetMethods = parseNitNonNullAnnotations()

    /** parse annotations produced by Nit and @return the set of methods whose return values are always non-null */
    def parseNitNonNullAnnotations() : Set[String] = {
      // potentially unsound, but reasonable annots to reduce false positives. can fix some of these by using Droidel's
      // instrumentation functionality
      val unsoundAnnots =
        Set("Landroid/view/View.findViewById(I)Landroid/view/View;",
            "Landroid/content/Context.getSystemService(Ljava/lang/String;)Ljava/lang/Object;",
            "Landroid/app/Activity.getSystemService(Ljava/lang/String;)Ljava/lang/Object;",
            "Landroid/content/Context.getResources()Landroid/content/res/Resources;",
            "Landroid/view/ContextThemeWrapper.getResources()Landroid/content/res/Resources;",
            "Landroid/content/res/Resources.getDrawable(I)Landroid/graphics/drawable/Drawable;",
            "Landroid/view/Window.findViewById(I)Landroid/view/View;"
        )

      // set of library methods that are known to return non-null values, but use native code or reflection that confuse
      // Nit / the analysis
      val libraryAnnots =
        Set("Ljava/lang/Integer.valueOf(I)Ljava/lang/Integer;",
            "Ljava/lang/StringBuilder.append(Ljava/lang/String;)Ljava/lang/StringBuilder;",
            "Landroid/content/ContentResolver.openInputStream(Landroid/net/Uri;)Ljava/io/InputStream;"
           )

      val defaultAnnots = libraryAnnots ++ unsoundAnnots
      val nitXmlFile = new File(s"$appPath/nit_annots.xml")
      if (nitXmlFile.exists()) {
        println(s"Parsing Nit annotations from ${nitXmlFile.getAbsolutePath}")
        (XML.loadFile(nitXmlFile) \\ "class").foldLeft (defaultAnnots) ((s, c) =>
          (c \\ "method").foldLeft (s) ((s, m) => {
            val ret = m \\ "return"
            if (ret.isEmpty || (ret \\ "NonNull").isEmpty) s
            else {
              val className = c.attribute("name").head.text
              // Nit separates method names from method signatures using colons; parse it out
              val parsedArr = m.attribute("descriptor").head.text.split(":")
              val (methodName, methodSig) = (parsedArr(0), parsedArr(1))
              val walaifedName = s"${ClassUtil.walaifyClassName(className)}.$methodName${methodSig.replace('.', '/')}"
              // using strings rather than MethodReference's to avoid classloader issues
              s + walaifedName
            }
          })
        )
      } else {
        println("No Nit annotations found")
        defaultAnnots
      }
    }

    // use Nit annotations to get easy refutation when we have a null constraint on a callee with a known non-null
    // return value
    override def tryBindReturnValue(call : SSAInvokeInstruction, qry : Qry, caller : CGNode,
                                    callee : CGNode) : Option[MSet[LocalPtEdge]] = {
      val calleeLocalConstraints = Util.makeSet[LocalPtEdge]
      val m = callee.getMethod
      val methodIdentifier = s"${ClassUtil.pretty(m.getDeclaringClass)}.${m.getSelector}"
      // check the Nit annotations to see if callee has a non-null annotation
      val calleeHasNonNullAnnotation = nonNullRetMethods.contains(methodIdentifier)

      if (call.hasDef) // x = call m(a, b, ...)
        getConstraintEdgeForDef(call, qry.localConstraints, caller) match {
          case Some(LocalPtEdge(_, p@PureVar(t))) if calleeHasNonNullAnnotation && t.isReferenceType && qry.isNull(p) =>
            if (Options.PRINT_REFS) println(s"Refuted by Nit annotation on ${ClassUtil.pretty(callee)}")
            None
          case Some(edge) => // found return value in constraints
            qry.removeLocalConstraint(edge) // remove x -> A constraint
            // add ret_callee -> A constraint
            calleeLocalConstraints += PtEdge.make(Var.makeReturnVar(callee, hm), edge.snk)
            Some(calleeLocalConstraints)
          case None => Some(calleeLocalConstraints) // return value not in constraints, no need to do anything
        }
      else Some(calleeLocalConstraints)
    }

  }

  lazy val exec =
    if (Options.PIECEWISE_EXECUTION) new DefaultPiecewiseSymbolicExecutor(tf, rr) {

      // TODO: do we want this?
      override val keepLoopConstraints = true

      // TODO: if callee is relevant to heap constraint only, choose to jump instead of diving in?
      override def returnFromCall(p : Path) : Iterable[Path] =
        if (p.callStackSize == 1 && isEntrypointCallback(p.node)) {
          println(s"at function boundary of entrypoint cb ${p.node}")
          val jmpPath = p.deepCopy
          val qry = jmpPath.qry
          // drop all local constraints
          qry.localConstraints.clear()

          // only keep constraints on null
          // TODO: keep access paths of constraints on null as well?
          qry.heapConstraints.foreach(e => e match {
            case e@ObjPtEdge(_, _, p@PureVar(_)) if qry.isNull(p) => ()
            case e@StaticPtEdge(_, _, p@PureVar(_)) if qry.isNull(p) => ()
            case _ => qry.removeHeapConstraint(e)
          })

          if (piecewiseJumpRefuted(jmpPath)) List.empty[Path] else super.returnFromCall(p)
        } else super.returnFromCall(p)

      override def forkToPredecessorBlocks(instrPaths : List[Path], startBlk : ISSABasicBlock,
                                           loopHeader : Option[ISSABasicBlock], ir : IR, passPaths : List[Path],
                                           failPaths : List[Path], test : Path => Boolean) =
        super.forkToPredecessorBlocksNoJump(instrPaths, startBlk, loopHeader, ir, passPaths, failPaths, test)

      override def shouldJump(p : Path) : Option[(Path, Qry => Boolean, Unit => Any)] =
        Some((p.deepCopy, ((q : Qry) => true), Util.NOP))

      override def executeInstr(paths : List[Path], instr : SSAInstruction, blk : ISSABasicBlock, node : CGNode,
                                cfg : SSACFG, isLoopBlk : Boolean, callStackSize : Int) : List[Path] = instr match {
        case i : SSAInvokeInstruction if !i.isStatic =>
          val okPaths =
            paths.filter(p =>
              PtUtil.getConstraintEdge(Var.makeLPK(i.getReceiver(), p.node, walaRes.hm), p.qry.localConstraints) match {
                case Some(LocalPtEdge(_, pv@PureVar(_))) if p.qry.isNull(pv) =>
                  // y is null--we could never have reached the current program point because executing this instruction would
                  // have thrown a NPE
                  if (Options.PRINT_REFS) println("Refuted by dominating null check!")
                  false
                case _ => true
              }
            )
          if (okPaths.isEmpty) Nil
          else super.executeInstr(okPaths, instr, blk, node, cfg, isLoopBlk, callStackSize)
        case _ => super.executeInstr(paths, instr, blk, node, cfg, isLoopBlk, callStackSize)
      }

    }
    else new DefaultSymbolicExecutor(tf)

  /* @return true if @param i can perform a null dereference */
  def canDerefFail(i : SSAInstruction, n : CGNode, hm : HeapModel, count : Int) = {
    val ir = n.getIR()
    val srcLine = IRUtil.getSourceLine(i, ir)
    print(s"Checking possible null deref #$count ")
    ClassUtil.pp_instr(i, ir); println(s" at source line $srcLine of ${ClassUtil.pretty(n)}")
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
    print(s"Deref #$count ")
    ClassUtil.pp_instr(i, ir)
    println(s" at source line $srcLine of ${ClassUtil.pretty(n)} can fail? $foundWitness")

    foundWitness
  }

  def isEntrypointCallback(n : CGNode) : Boolean =
    !ClassUtil.isLibrary(n) && walaRes.cg.getPredNodes(n).exists(n => ClassUtil.isLibrary(n))

  def checkForRacingDerefs() = {
    import walaRes._
    /*val id = new AbsurdityIdentifier("")
    val absurdities = id.getAbsurdities(walaRes, reportLibraryAbsurdities = false)
    println(s"Have ${absurdities.size} absurdities")*/

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

    def shouldCheck(n : CGNode) : Boolean =
      n.getMethod.getDeclaringClass.getName.toString.contains("DuckDuckGo") && n.getMethod.getName.toString == "onPreferenceChange" && // TODO: TMP, for testing
      !ClassUtil.isLibrary(n)

    val nullDerefs =
      walaRes.cg.foldLeft (0) ((count, n) =>
        if (shouldCheck(n)) n.getIR match {
          case null => count
          case ir =>
            ir.getInstructions.foldLeft (count) ((count, i) => i match {
              case i : SSAInvokeInstruction if !i.isStatic && !IRUtil.isThisVar(i.getReceiver) &&
                                               !i.getDeclaredTarget.isInit =>
                if (canDerefFail(i, n, walaRes.hm, count)) count + 1
                else count

              case i : SSAFieldAccessInstruction if !i.isStatic && !IRUtil.isThisVar(i.getRef) =>
                if (canDerefFail(i, n, walaRes.hm, count)) count + 1
                else count

              case _ => count
            })
        } else count
      )

    println(s"Found $nullDerefs potential null derefs")
  }
}
