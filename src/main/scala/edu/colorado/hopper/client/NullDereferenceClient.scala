package edu.colorado.hopper.client

import java.io.File

import com.ibm.wala.classLoader.{IField, IMethod}
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.callgraph.propagation._
import com.ibm.wala.ssa._
import com.ibm.wala.types.TypeReference
import edu.colorado.hopper.executor.{DefaultSymbolicExecutor, TransferFunctions}
import edu.colorado.hopper.jumping.{DefaultJumpingSymbolicExecutor, JumpingTransferFunctions, RelevanceRelation}
import edu.colorado.hopper.state._
import edu.colorado.hopper.util.PtUtil
import edu.colorado.thresher.core.Options
import edu.colorado.walautil._

import scala.collection.JavaConversions._
import scala.io.Source
import scala.xml.XML

// TODO: refactor this to combine with/share code with Android nulls client
/* specialized null dereference client that only checks for null derefs on fields/locals assigned to null literals at
 * some point during program execution */
class NullDereferenceClient(appPath : String, libPath : Option[String], mainClass : String, mainMethod : String, 
    isRegression : Boolean = false) extends Client(appPath, libPath, mainClass, mainMethod, isRegression) {

   // if true, report derefs as safe if they are guarded by an appropriate catch block
   val suppressCaughtExceptions = false

   def parseProveList(fileName : String) : Set[Int] =
    if (new File(fileName).exists()) {
      val f  = Source.fromFile(fileName)
      val proven = f.getLines.foldLeft (Set.empty[Int]) ((set, line) => 
        if (line.contains("can fail? false")) {
          val derefStr = "Deref # "
          val index = line.indexOf(derefStr)
          val numStr = line.substring(index + derefStr.length(), line.indexOf(" v"))
          set + numStr.toInt
        } 
        else set
      )
      f.close
      proven
    }
    else {
      println("File " + fileName + " does not exist.")
      Set.empty[Int]
    }  
  
  def checkNullDerefs() : (Int, Int) = {
    // for dacapo only
    val proveSetFile = s"out_${Options.APP.substring(Options.APP.lastIndexOf('/') + 1)}.txt"
    println(proveSetFile)
    val proveSet = parseProveList(proveSetFile)
    println("proveSet size is " + proveSet.size)
    
    val walaRes = makeCallGraphAndPointsToAnalysis
    val exec =
      if (Options.JUMPING_EXECUTION) {
        val rr = new RelevanceRelation(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha)
        val tf = new JumpingTransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha, rr)
        new DefaultJumpingSymbolicExecutor(tf, rr)
      } else
        new DefaultSymbolicExecutor(new NullDereferenceTransferFunctions(walaRes)) {
          override def executeInstr(paths : List[Path], instr : SSAInstruction, blk : ISSABasicBlock, node : CGNode,
                                    cfg : SSACFG, isLoopBlk : Boolean, callStackSize : Int) : List[Path] = instr match {
            case i : SSAInvokeInstruction if !i.isStatic =>
              val okPaths =
                paths.filter(p =>
                  PtUtil.getConstraintEdge(Var.makeLPK(i.getReceiver(), p.node, walaRes.hm), p.qry.localConstraints) match {
                    case Some(LocalPtEdge(_, pv@PureVar(_))) if p.qry.isNull(pv) =>
                      // y is null--we could never have reached the current program point because executing this
                      // instruction would have thrown a NPE
                      if (Options.PRINT_REFS) println("Refuted by dominating null check!")
                      false
                    case _ => true
                  }
                )
              if (okPaths.isEmpty) Nil
              else {
                val retPaths = super.executeInstr(okPaths, i, blk, node, cfg, isLoopBlk, callStackSize)
                if (!i.isStatic) {
                  val receiverLPK = Var.makeLPK(i.getReceiver, node, tf.hm)
                  retPaths.foreach(p => if (!p.isInJump &&
                                            p.qry.localMayPointIntoQuery(receiverLPK, node, tf.hm, tf.hg, tf.cha)) {
                    PtUtil.getPt(receiverLPK, tf.hg) match {
                      case rgn if rgn.isEmpty => sys.error("handle this case!") // should lead to a refutation
                      case rgn =>
                        // add constraint y != null (effectively)
                        p.qry.addLocalConstraint(PtEdge.make(receiverLPK, ObjVar(rgn)))
                    }
                  })
                }
                retPaths
              }
            case _ => super.executeInstr(paths, instr, blk, node, cfg, isLoopBlk, callStackSize)
          }
        }

    val cg = walaRes.cg
    val hm = walaRes.hm
    val cha = walaRes.cha
    val hg = walaRes.hg
    
    // don't check Dacapo harness methods
    def shouldIgnore(n : CGNode) : Boolean =
      n.getMethod().getDeclaringClass().getName().toString().startsWith("Ldacapo")
    
    val filteredCg = cg.filter(n => !ClassUtil.isLibrary(n) && !shouldIgnore(n) && n.getIR() != null)
    val dangerKeys = filteredCg.foldLeft (Set.empty[InstanceKey]) ((dangerKeys, n) => {
      val ir = n.getIR()
      val instrs = ir.getInstructions().toIterable
      val tbl = ir.getSymbolTable()
      // get all instructions of the form x.f = null
      instrs.foldLeft (dangerKeys) ((dangerKeys, i) => i match { 
        //case i : SSAPhiInstruction => if (0 to i.getNumberOfUses()).exists(i => tbl.isNullConstant(i)) =>
          //PtUtil.getPt(Var.makeLPK(i.getDef(), n, hm), hg) ++ dangerKeys
        case i : SSAPutInstruction if tbl.isNullConstant(i.getVal()) =>          
                    val srcLine = IRUtil.getSourceLine(i, ir)
          print(s"Creating danger key because of "); ClassUtil.pp_instr(i, ir); println(s" at source line $srcLine of ${ClassUtil.pretty(n)}")            
          val f = cha.resolveField(i.getDeclaredField())
          // get pt(x)
          val ptX = 
            if (i.isStatic()) PtUtil.getPt(hm.getPointerKeyForStaticField(f), hg) 
            else PtUtil.getPt(Var.makeLPK(i.getRef(), n, hm), hg)
          // get pt(x.f); that is, find out what else x.f can hold besides null
          PtUtil.getPtI(ptX, f, hg) ++ dangerKeys
        case _ => dangerKeys
      })
    }).filterNot(k => k.isInstanceOf[ConcreteTypeKey]) // these are too noisy
    
    println(s"Found ${dangerKeys.size} danger keys.")
    
    // TODO: could optimize with a type-based check instead of going straight to PT
    def mayHoldDangerKey(useNum : Int, n : CGNode, tbl : SymbolTable) : Boolean = {
      /*val locPt = PtUtil.getPt(Var.makeLPK(useNum, n, hm), hg)
      !locPt.intersect(dangerKeys).isEmpty*/
      true // checks all derefs rather than just "danger key" derefs
    }
        
    def canBeNullDeref(useNum : Int, i : SSAInstruction, n : CGNode, count : Int) : Boolean = 
      if (proveSet.contains(count)) { 
        println(s"Skipping possible null deref # ${count} due to prove set")
        false
      } else if (Options.SOUND_EXCEPTIONS && suppressCaughtExceptions && {
          val ir = n.getIR
          val startBlk = ir.getBasicBlockForInstruction(i)
          CFGUtil.isProtectedByCatchBlockInterprocedural(startBlk, n,
            TypeReference.JavaLangNullPointerException, cg, cha)
        }) {
          println("Exception analysis proved null deref safe.")
          false
      } else {
        val ir = n.getIR()
        val srcLine = IRUtil.getSourceLine(i, ir)
        print(s"Checking possible null deref # ${count} "); ClassUtil.pp_instr(i, ir); println(s" at source line $srcLine of ${ClassUtil.pretty(n)}")
        // create the query
        val lpk = Var.makeLPK(useNum, n, hm)
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
              println(s"Error on access # $count $e \n${e.getStackTraceString}")
              if (Options.DEBUG) throw e
              else true // soundly assume we got a witness
          }
        print(s"Deref # $count "); ClassUtil.pp_instr(i, ir); println(s" at source line $srcLine of ${ClassUtil.pretty(n)} can fail? $foundWitness")
        foundWitness
    }    

    // now, every time there is a field read of, field write to, or method call on a value in dangerKeys, we will check it           
    val (proven, total) = filteredCg.foldLeft (0, 0) ((statsPair, n) => {
      val ir = n.getIR
      val instrs = ir.getInstructions().toIterable
      val tbl = ir.getSymbolTable()
      instrs.foldLeft (statsPair) ((statsPair, i) => i match {
        case i : SSAFieldAccessInstruction if !i.isStatic() && !IRUtil.isThisVar(i.getRef()) &&
                                              mayHoldDangerKey(i.getRef(), n, tbl) =>
          val numProven = (if (canBeNullDeref(i.getRef(), i, n, statsPair._2)) 0 else 1) + statsPair._1
          (numProven, statsPair._2 + 1)
        case i : SSAInvokeInstruction if !i.isStatic() && !i.getDeclaredTarget().isInit() &&
                                         !tbl.isStringConstant(i.getReceiver) && !IRUtil.isThisVar(i.getReceiver()) &&
                                         mayHoldDangerKey(i.getReceiver(), n, tbl) =>
          val numProven = (if (canBeNullDeref(i.getReceiver(), i, n, statsPair._2)) 0 else 1) + statsPair._1
          (numProven, statsPair._2 + 1)
        case _ => statsPair
      })      
    }) 
    
    println(s"Checked $total null derefs, proved $proven safe.")    
    (proven, total)
  }
}

class NullDereferenceTransferFunctions(walaRes : WalaAnalysisResults,
                                       nitAnnotsXmlFile : File = new File("nit_annots.xml"))
  extends TransferFunctions(walaRes.cg, walaRes.hg, walaRes.hm, walaRes.cha) {

  override def execute(s : SSAInstruction, qry : Qry, n : CGNode) : List[Qry] = s match {
    case i: SSAGetInstruction if !i.isStatic =>
      getConstraintEdgeForDef(i, qry.localConstraints, n) match {
        case Some(LocalPtEdge(_, p@PureVar(_))) if qry.isNull(p) =>
          val fld = i.getDeclaredField
          if (ClassUtil.isInnerClassThis(fld)) {
            // have x == null and x = y.this$0 (or similar). reading from this$0 will never return null without bytecode
            // editor magic (or order of initialization silliness)--refute
            if (Options.PRINT_REFS) println("Refuted by read from inner class this!")
            Nil
          } else
            cha.resolveField(fld) match {
              case null => super.execute (s, qry, n)
              case fld =>
                if (hasNitNonNullFieldAnnotation(fld)) {
                  if (Options.PRINT_REFS) println ("Refuted by nit annotation on field!")
                  Nil
                } else super.execute (s, qry, n)
            }
        case _ => super.execute(s, qry, n)
      }
    case i: SSAFieldAccessInstruction if !i.isStatic() => // x = y.f or y.f = x
      val refLPK = Var.makeLPK(i.getRef(), n, hm)
      PtUtil.getConstraintEdge(refLPK, qry.localConstraints) match {
        case Some(LocalPtEdge(_, p@PureVar(_))) if qry.isNull(p) =>
          // y is null--we could never have reached the current program point because executing this instruction would
          // have thrown a NPE
          if (Options.PRINT_REFS) println("Refuted by dominating null check!")
          Nil
        case Some(e) => super.execute(s, qry, n)
        case None =>
          val retPaths = super.execute(s, qry, n)
          val tbl = n.getIR.getSymbolTable
          retPaths.filter(qry =>
            if (tbl.isConstant(i.getRef)) true
            else {
              // have to check for edge again here because it may be added by call to super.execute()
              PtUtil.getConstraintEdge(refLPK, qry.localConstraints) match {
                case None if qry.localMayPointIntoQuery(refLPK, n, hm, hg, cha) =>
                  PtUtil.getPt(refLPK, hg) match {
                    case rgn if rgn.isEmpty => false // should leak to a refutation
                    case rgn =>
                      // add constraint y != null (effectively)
                      qry.addLocalConstraint(PtEdge.make(refLPK, ObjVar(rgn)))
                      true
                  }
                case _ => true
              }
            }
          )
      }
    case i : SSAGetInstruction => // i is static
      if (ClassUtil.isEnum(i.getDeclaredField.getDeclaringClass, cha))
        getConstraintEdgeForDef(i, qry.localConstraints, n) match {
          case Some(LocalPtEdge(_, p@PureVar(_))) if qry.isNull(p) =>
            // we are reading a static field from an Enum class; it is a member of the declared Enum and guaranteed not
            // to be null based on the way that the Java compiler generates code for enums. refute
            if (Options.PRINT_REFS) println("Refuted by enum not null!")
            Nil
          case _ => super.execute(s, qry, n)
        }
      else super.execute(s, qry, n)
    case i : SSAInvokeInstruction if !i.isStatic() => // x = y.m(...)
      sys.error("This case should be handled in SymbolicExcutor.executeInstr")
    case _ => super.execute(s, qry, n)
  }

  private val (nonNullRetMethods, nonNullFields) = parseNitNonNullAnnotations()

  /** parse annotations produced by Nit and @return the set of methods whose return values are always non-null */
  def parseNitNonNullAnnotations() : (Set[String],Set[String]) = {
    // set of Java library methods that are known to return non-null values, but use native code or reflection that
    // confuse Nit / the analysis
    val javaAnnots =
      Set("Ljava/lang/Integer.valueOf(I)Ljava/lang/Integer;",
          "Ljava/lang/Object.toString()Ljava/lang/String;",
          "Ljava/lang/StringBuilder.append(Z)Ljava/lang/StringBuilder;",
          "Ljava/lang/StringBuilder.append(C)Ljava/lang/StringBuilder;",
          "Ljava/lang/StringBuilder.append([C)Ljava/lang/StringBuilder;",
          "Ljava/lang/StringBuilder.append(I)Ljava/lang/StringBuilder;",
          "Ljava/lang/StringBuilder.append(J)Ljava/lang/StringBuilder;",
          "Ljava/lang/StringBuilder.append(Ljava/lang/CharSequence;)Ljava/lang/StringBuilder;",
          "Ljava/lang/StringBuilder.append(Ljava/lang/String;)Ljava/lang/StringBuilder;",
          "Ljava/lang/StringBuilder.append(Ljava/lang/StringBuffer;)Ljava/lang/StringBuilder;",
          "Ljava/lang/ThreadLocal.get()Ljava/lang/Object;"
      )

    // similar story for Android library methods. unlike the java annotations, some of these annots are potentially
    // unsound, but are generally reasonable and/or required to eliminate dumb false positives. can fix some of these by
    // using Droidel's instrumentation functionality (i.e., for findViewByID)
    val androidAnnots =
      Set("Landroid/app/Activity.findViewById(I)Landroid/view/View;",
          "Landroid/app/Activity.getFragmentManager()Landroid/app/FragmentManager;",
          "Landroid/app/Activity.getSystemService(Ljava/lang/String;)Ljava/lang/Object;",
          "Landroid/app/Activity.getIntent()Landroid/content/Intent;",
          "Landroid/app/Activity.getWindow()Landroid/view/Window;",
          "Landroid/content/ContentResolver.openInputStream(Landroid/net/Uri;)Ljava/io/InputStream;",
          "Landroid/content/Context.getResources()Landroid/content/res/Resources;",
          "Landroid/content/Context.getSystemService(Ljava/lang/String;)Ljava/lang/Object;",
          "Landroid/content/res/Resources.getDrawable(I)Landroid/graphics/drawable/Drawable;",
          "Landroid/content/res/Resources.getText(I)Ljava/lang/CharSequence",
          "Landroid/view/ContextThemeWrapper.getResources()Landroid/content/res/Resources;",
          "Landroid/view/View.findViewById(I)Landroid/view/View;",
          "Landroid/view/View.getResources()Landroid/content/res/Resources;",
          "Landroid/view/Window.findViewById(I)Landroid/view/View;",
          "Landroid/widget/TextView.getText()Ljava/lang/CharSequence;",
          // TODO: get rid of these eventually. calling getActivity() in the wrong place in a Fragment is sometimes a
          // source of bugs, but more commonly a source of false alarm. it takes a deep understanding of the lifecycle
          // to tell the difference. pragmatically ignoring for now
          "Landroid/support/v4/app/Fragment.getActivity()Landroid/support/v4/app/FragmentActivity;",
          "Landroid/app/Fragment.getActivity()Landroid/app/Activity;"
      )

    val defaultMethodAnnots = javaAnnots ++ androidAnnots
    if (nitAnnotsXmlFile.exists()) {
      println(s"Parsing Nit annotations from ${nitAnnotsXmlFile.getAbsolutePath}")
      (XML.loadFile(nitAnnotsXmlFile) \\ "class").foldLeft (defaultMethodAnnots, Set.empty[String]) ((pair, c) => {
        val (methodAnnots, fieldAnnots) = pair
        val className = ClassUtil.walaifyClassName(c.attribute("name").head.text)
        val newMethodAnnots = (c \\ "method").foldLeft(methodAnnots)((s, m) => {
          val ret = m \\ "return"
          if (ret.isEmpty || (ret \\ "NonNull").isEmpty) s
          else {
            // Nit separates method names from method signatures using colons; parse it out
            val parsedArr = m.attribute("descriptor").head.text.split(":")
            val (methodName, methodSig) = (parsedArr(0), parsedArr(1))
            val walaifedName = s"$className.$methodName${methodSig.replace('.', '/')}"
            // using strings rather than MethodReference's to avoid classloader issues
            s + walaifedName
          }
        })
        val newFieldAnnots = (c \\ "field").foldLeft (fieldAnnots) ((s, f) => {
          if (f.isEmpty || (f \\ "NonNull").isEmpty) s
          else {
            val parsedArr = f.attribute("descriptor").head.text.split(":")
            val fldName = parsedArr(0)
            val walaifedName = s"$className.$fldName"
            s + walaifedName
          }
        })
        (newMethodAnnots, newFieldAnnots)
      })
    } else {
      println("No Nit annotations found")
      (defaultMethodAnnots, Set.empty[String])
    }
  }

  private def getNitMethodIdentifier(m : IMethod) =
    s"${ClassUtil.pretty(m.getDeclaringClass)}.${m.getSelector}"

  private def getNitFieldIdentifier(f : IField) =
    s"${ClassUtil.pretty(f.getDeclaringClass)}.${f.getName.toString}"

  def hasNitNonNullReturnAnnotation(m : IMethod) : Boolean = nonNullRetMethods.contains(getNitMethodIdentifier(m))

  def hasNitNonNullFieldAnnotation(f : IField) : Boolean = nonNullFields.contains(getNitFieldIdentifier(f))

  override def isDispatchFeasible(call : SSAInvokeInstruction, caller : CGNode, p : Path) : Boolean =
    call.isStatic || {
      val qry = p.qry
      val receiverLPK = Var.makeLPK(call.getReceiver, caller, hm)
      PtUtil.getConstraintEdge(receiverLPK, qry.localConstraints) match {
        case Some(LocalPtEdge(_, p@PureVar(_))) if qry.isNull(p) => false // refuted by null dispatch
        case None if qry.localMayPointIntoQuery(receiverLPK, caller, hm, hg, cha) =>
          PtUtil.getPt(receiverLPK, hg) match {
            case rgn if rgn.isEmpty => false // refuted by null dispatch
            case rgn =>
              val tbl = caller.getIR.getSymbolTable
              if (tbl.isNullConstant(call.getReceiver)) false
              else {
                if (!tbl.isConstant(call.getReceiver) && !p.isInJump)
                  qry.addLocalConstraint(PtEdge.make(receiverLPK, ObjVar(rgn)))
                true
              }
          }
        case _ => true
      }
    }

  // use Nit annotations to get easy refutation when we have a null constraint on a callee with a known non-null retval
  override def isRetvalFeasible(call : SSAInvokeInstruction, caller : CGNode, callee : CGNode, p : Path) : Boolean =
    !call.hasDef || !call.getDeclaredResultType.isReferenceType || {
      val qry = p.qry
      val m = callee.getMethod
      if (hasNitNonNullReturnAnnotation(m))
        getConstraintEdgeForDef(call, qry.localConstraints, caller) match {
          case Some(LocalPtEdge(_, p@PureVar(_))) if qry.isNull(p) =>
            if (Options.PRINT_REFS) println(s"Refuted by Nit annotation on ${ClassUtil.pretty(callee)}")
            false
          case _ => true
        }
      else super.isRetvalFeasible(call, caller, callee, p)
    }

}