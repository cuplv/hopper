package edu.colorado.hopper.executor

import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.analysis.reflection.CloneInterpreter
import com.ibm.wala.classLoader.{IClass, IField}
import com.ibm.wala.ipa.callgraph.propagation.{ConcreteTypeKey, HeapModel, InstanceKey, LocalPointerKey, PointerKey}
import com.ibm.wala.ipa.callgraph.{CGNode, CallGraph}
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ipa.modref.{DelegatingExtendedHeapModel, ModRef}
import com.ibm.wala.ssa._
import com.ibm.wala.types.TypeReference
import com.ibm.wala.util.graph.traverse.DFS
import edu.colorado.hopper.executor.TransferFunctions._
import edu.colorado.hopper.solver.UnknownSMTResult
import edu.colorado.hopper.state._
import edu.colorado.hopper.synthesis.InterfaceMethodField
import edu.colorado.hopper.util.PtUtil
import edu.colorado.hopper.util.PtUtil._
import edu.colorado.thresher.core.Options
import edu.colorado.walautil.Types._
import edu.colorado.walautil.{ClassUtil, Util}

import scala.collection.JavaConversions._

object TransferFunctions {  
  def DEBUG = Options.SCALA_DEBUG
  // print warning messages about potential unsoundness in the points-to analysis
  private val EMPTY_PT_WARNING = true 
  
   def initializeStaticFieldsToDefaultValues(qry : Qry, node : CGNode) : Boolean = {
    require(node.getMethod().isClinit() || node.getMethod().isSynthetic(), "Expecting clinit method, got " + ClassUtil.pretty(node))
    val method = node.getMethod()
    val staticFlds = if (method.isClinit()) method.getDeclaringClass().getDeclaredStaticFields().toSet
    else // node is fakeWorldClinit rather than any particular class initializer.
      // WALA doesn't necessarily generate a clinit method for all clxasses, but we still need to initialize the
      // static fields of these classes to their default values. we accomplish this by calling this method
      // with node as fakeWorldClinit
      qry.heapConstraints.collect({ case StaticPtEdge(src, fld, snk) => fld.fld.getField() })

    !qry.heapConstraints.exists(e => e match {
      case e@StaticPtEdge(src, fld, snk) if staticFlds.contains(fld.fld.getField()) =>
        snk match {
        case p@PureVar(_) =>
          qry.removeHeapConstraint(e)
          !qry.addPureConstraint(Pure.makeDefaultValConstraint(p))
        case _ => 
          assert(fld.fld.getField().getFieldTypeReference().isReferenceType())
          // must be an reference type, and thus is initialized to default value null
          // since we had a constraint o.f -> A (and A is implicitly non-null by construction
          // conventions of our constraint representation), this is a refutation
          if (Options.PRINT_REFS) println("Refuted by static fields init to default vals (ref -> null)!")
          true
      }       
      case _ => false
    })
  }
  
  def initializeInstanceFieldsToDefaultValues(qry : Qry, constructor : CGNode, thisPT : Set[ObjVar]) : Boolean = {
    //println("INIT TO DEFAULT VALS FOR " + qry.id + "Q method " + ClassUtil.pretty(constructor))
    val instanceFlds = constructor.getMethod().getDeclaringClass().getDeclaredInstanceFields()
    
    !qry.heapConstraints.exists(e => e match {
      // TODO: arrays and array elements to default vals
      case e@ObjPtEdge(src, fld, snk) if thisPT.contains(src) && instanceFlds.contains(fld.fld) => snk match {
        case p@PureVar(_) =>
          qry.removeHeapConstraint(e)
          !qry.addPureConstraint(Pure.makeDefaultValConstraint(p))
        case _ => 
          assert(fld.fld.getFieldTypeReference().isReferenceType())
          // must be an reference type, and thus is initialized to default value null
          // since we had a constraint o.f -> A (and A is implicitly non-null by construction
          // conventions of our constraint representation), this is a refutation
          if (Options.PRINT_REFS) println("Refuted by instance fields init to default vals (ref -> null)!")
          true
        }      
      case e@ArrayPtEdge(src, _, snk) if thisPT.contains(src) => snk match {
        case p@PureVar(_) =>
          qry.removeHeapConstraint(e)
          !qry.addPureConstraint(Pure.makeDefaultValConstraint(p))
        case _ => sys.error("Expecting PureVar, got " + snk)
      }
      case _ => false
    })
  } 
  
}

/** implements the |- {R} c {Q} judgement from Section 3.2 of Thresher: Precise Refutations for Heap Reachability (PLDI 2013) */
class TransferFunctions(val cg : CallGraph, val hg : HeapGraph[InstanceKey], _hm : HeapModel, val cha : IClassHierarchy) {
  val hm = new DelegatingExtendedHeapModel(_hm)
  val modRef = ModRef.make().computeMod(cg, hg.getPointerAnalysis)
  
  /** look up the lhs of @param s in @param localConstraints, @return matching rhs var and edge if we find it */
  protected def getConstraintPtForDef(s : SSAInstruction, localConstraints : MSet[LocalPtEdge], n : CGNode) : Option[(ObjVar,LocalPtEdge)] =
    getConstraintPt(Var.makeLPK(s.getDef(), n, hm), localConstraints)  
  
  protected def getConstraintEdgeForDef(s : SSAInstruction, localConstraints : MSet[LocalPtEdge], n : CGNode) : Option[LocalPtEdge] =
    getConstraintEdge(Var.makeLPK(s.getDef(), n, hm), localConstraints)
    
  protected def getConstraintEdgeForRet(localConstraints : MSet[LocalPtEdge], n : CGNode) : Option[LocalPtEdge] =
    getConstraintEdge(Var.makeRVK(n, hm), localConstraints)
  
  protected def getConstraintEdgeForStaticFld(fld : IField, heapConstraints : MSet[HeapPtEdge], hm : HeapModel) : Option[HeapPtEdge] = {
    val classVar = ClassVar(fld.getDeclaringClass())
    val staticFld = Fld.makeStaticFld(fld, hm)
    heapConstraints.find(edge => edge.src == classVar && edge.fld == staticFld)
  }
  
  private def getPureExprForLocal(useNum : Int, qry : Qry, n : CGNode, hm : HeapModel) : PureExpr = getPureExprForLocal(Var.makeLPK(useNum, n, hm), qry)
  
  // get rhs of edge with l as LHS if it exists, otherwise create fresh PureVar and add edge l -> pureVar edge
  private def getPureExprForLocal(l : LocalPointerKey, qry : Qry) : PureExpr = getConstraintEdge(l, qry.localConstraints) match { 
    case Some(e) => e.snk match { // already have edge
      case snk : PureExpr => snk
      case other => sys.error("expected snk to be pure expr; got " + e)
    }
    case None => // do not have edge; create it
      getPureExprForLocalInternal(l, qry)      
  }
  
  // only call this if the query has no constraint on l
  def getPureExprForLocalInternal(l : LocalPointerKey, qry : Qry) : PureExpr = {
    val tbl = l.getNode().getIR().getSymbolTable()
    if (tbl.isConstant(l.getValueNumber())) Pure.makePureVal(tbl, l.getValueNumber()) // create constant
    else { // non-constant, create var
      val freshVar = Pure.makePureVar(l) 
      qry.addLocalConstraint(PtEdge.make(l, freshVar)) // add l -> freshVar constraint
      freshVar
    }
  }
  
  private def getSnkAsObjVar(e : PtEdge) : ObjVar = e.snk match {
    case obj@ObjVar(_) => obj
    case _ => sys.error("Expecting ObjVar as snk of " + e)
  }
  
  private def getSnkAsPureVar(e : PtEdge) : PureVar = e.snk match {
    case p@PureVar(_) => p
    case _ => sys.error("Expecting PureVar as snk of " + e)
  }
  
  def executePhi(phi : SSAPhiInstruction, phiIndex : Int, qry : Qry, n : CGNode) : Boolean = // x = phi(y_i), i = phiIndex
    getConstraintEdgeForDef(phi, qry.localConstraints, n) match {
     case Some(xEdge) => // found edge x -> A
       qry.removeLocalConstraint(xEdge) // remove x -> A edge
       val phiUse = phi.getUse(phiIndex)
       val useKey = Var.makeLPK(phiUse, n, hm)  
       val tbl = n.getIR().getSymbolTable()
       if (tbl.isConstant(phiUse)) 
         if (tbl.isNullConstant(phiUse)) xEdge.snk match {
           case ObjVar(_) => 
             if (DEBUG) println("Refuted by assignment to null (phi!)")
             false
           case p@PureVar(_) => 
             val qrySaysNull = qry.isNull(p)
             if (!qrySaysNull && DEBUG) println("Refuted by assignment to null (phi!)")
             qrySaysNull
         } else xEdge.snk match {
           case o@ObjVar(_) => true // this can happen if x -> [String] and the phiUse is a string constant
           case p@PureVar(_) => qry.addPureConstraint(Pure.makeEqConstraint(p, Pure.makePureVal(tbl, phiUse)))
         }
       else getPtVal(useKey, qry.localConstraints, hg) match {
         case (ptPhi@ObjVar(rgnPhi), edge) => 
           xEdge.snk match {
             case ptX@ObjVar(rgnX) =>
               val rgnInter = rgnPhi.intersect(rgnX)
               if (rgnInter.isEmpty) {
                 if (Options.PRINT_REFS) println("refuted by from empty in phi instruction")
                 false 
               } else {
                 // construct var from pt(x) \cap pt(y_i)
                 val interVar = ObjVar(rgnInter)
                 // remove y -> interVar edge if it existed
                 if (edge.isDefined) qry.removeLocalConstraint(edge.get)
                 qry.addLocalConstraint(PtEdge.make(useKey, interVar)) // add y -> interVar edge
                 if (!qry.substitute(interVar, ptX, hg)) false // sub interVar for pt(x)
                 else if (edge.isDefined) qry.substitute(interVar, ptPhi, hg) // sub interVar for pt(y_i) (it could already be in our constraints)
                 else true
              }
             case p@PureVar(_) => 
               if (edge.isDefined) qry.addPureConstraint(Pure.makeNeNullConstraint(p))
               else {
                 qry.addLocalConstraint(PtEdge.make(useKey, p))
                 true
               }
           }
            
         case (purePhi@PureVar(_), edge) => 
           xEdge.snk match {
             case ptX@ObjVar(rgnX) => 
               if (qry.isNull(purePhi)) false // refuted by assignment to null
               else {
                 qry.addLocalConstraint(PtEdge.make(useKey, ptX))
                 true
               }
             case p@PureVar(_) =>
               if (edge.isDefined) qry.addPureConstraint(Pure.makeEqConstraint(p, purePhi))
               else {
                 qry.addLocalConstraint(PtEdge.make(useKey, p))
                 true
               }               
           }/*
           edge match {
             case Some(LocalPtEdge(loc, p@PureVar(_))) =>
               // add A == B constraint and return result of SAT check . no need to add local constraint; already encoded in edge              
               qry.addPureConstraint(Pure.makeEqConstraint(purePhi, p))
             case None => // no matching edge
               assert(!n.getIR().getSymbolTable().isConstant(useKey.getValueNumber()))
               // this is a very odd case; y_i is not a constant (null or otherwise), but it's points-to set is empty
               // this either means that y_i is definitely null or that there is some kind of unsoundness in the points-to
               // analysis (due to reflection e.t.c). we handle this by doing nothing
               //qry.addLocalConstraint(PtEdge.make(useKey, purePhi))
               true
             case Some(edge) => sys.error("Expecting PureVar as snk of " + edge)               
           }    */   
       }
     case None => true // no matching edge in localConstraints
    }
   
  def constrainBasedOnSwitchCases(cases : Iterable[SSAConditionalBranchInstruction], qry : Qry, n : CGNode) : Boolean = {
    val tbl = n.getIR().getSymbolTable()
    val cond = cases.head
    assert(!tbl.isConstant(cond.getUse(0)))
    val lpk = Var.makeLPK(cond.getUse(0), n, hm)
    val pureSnk = getConstraintEdge(lpk, qry.localConstraints) match {
      case Some(LocalPtEdge(_, p@PureVar(_))) => p
      case None => 
        val p = Pure.makePureVar(lpk)
        qry.addLocalConstraint(PtEdge.make(lpk, p))
        p
      case e => sys.error("Unexpected edge " + e)
    }
    val disjunctiveCaseConstraint =
      Pure.makePureDisjunctiveConstraint(cases.foldLeft (Set.empty[PureAtomicConstraint]) ((s, _case) =>
        s + Pure.makeEqConstraint(pureSnk , Pure.makePureVal(tbl, _case.getUse(1)))))
    qry.addPureConstraint(disjunctiveCaseConstraint)
  }
  
  // we choose to refute based on empty PT
  def refuteBasedOnEmptyPT(lpk : LocalPointerKey, qry : Qry, n : CGNode) : Boolean = {
    if (EMPTY_PT_WARNING) println(s"(1) Warning: returning null for v${lpk.getValueNumber} based on empty PT set")
    true
  }
  
  def executeCond(cond : SSAConditionalBranchInstruction, qry : Qry, n : CGNode, isThenBranch : Boolean) : Boolean = {
    val tbl = n.getIR().getSymbolTable()
    val (use0, use1) = (cond.getUse(0), cond.getUse(1))
    val op = if (isThenBranch) cond.getOperator else Pure.negateCmpOp(cond.getOperator)
    val (use0Constant, use1Constant) = (tbl.isConstant(use0), tbl.isConstant(use1))
    // optimization - evaluate constant conditionals ourselves rather than passing them on to Z3
    if (use0Constant && use1Constant) Pure.evaluateConstConditional(tbl, cond) // comparison of constants
    else {
      if (cond.getType().isReferenceType()) { // conditional is y op z
        
        def handlePureToObjComparison(p : PureVar) = 
          // if p == null, this is only feasible if the conditional is o != p
          // if p != null, this is feasible (p could be anything)
          !qry.isNull(p) || Pure.isInequalityOp(op)
        
        def handleObjComparison(v0 : Val, v1 : Val) : Boolean = (v0, v1) match {
          case (o0@ObjVar(rgn0), o1@ObjVar(rgn1)) =>
            if (Pure.isEqualityOp(op)) {
              val rgnInter = rgn0.intersect(rgn1)
              if (rgnInter.isEmpty) false // refuted
              else {
                val interVar = ObjVar(rgnInter)
                qry.substitute(interVar, o0, hg) && qry.substitute(interVar, o1, hg)
              }
            } else o0 != o1 // conditional is true as long as these aren't the same var   
          case (p0@PureVar(_), p1@PureVar(_)) =>
            if (Pure.isEqualityOp(op)) qry.addPureConstraint(Pure.makeEqConstraint(p0, p1))
            else qry.addPureConstraint(Pure.makeNeConstraint(p0, p1)) 
          case (_, p@PureVar(_)) => handlePureToObjComparison(p)
          case (p@PureVar(_), _) => handlePureToObjComparison(p)
        }        
        
        def handleSingleObjComparison(e : LocalPtEdge, useNum : Int) : Boolean = {
          val nullConst = tbl.isNullConstant(useNum)
          val stringConst = tbl.isStringConstant(useNum)
          e.snk match {
            case o@ObjVar(_) => 
              if (nullConst) {
                val res = !Pure.isEqualityOp(op)
                if (!res && Options.PRINT_REFS) println("refuted by nullness in conditional!")
                res
              } else {
                val yLPK = Var.makeLPK(useNum, n, hm)
                val yVar = getPt(yLPK, hg) match {
                  case rgn if rgn.isEmpty =>
                    Qry.getNullVar(qry)
                  case rgn => ObjVar(rgn)
                }
                if (!stringConst) qry.addLocalConstraint(PtEdge.make(yLPK, yVar))
                handleObjComparison(o, yVar)
              }
            case p@PureVar(_) => // add eq / ne null constraint as appropriate
              if (nullConst) {
                val qrySaysNull = qry.isNull(p)
                if (Pure.isEqualityOp(op)) { // y == null constraint
                  if (!qrySaysNull && Options.PRINT_REFS) println("refuted by nullness in conditional!")
                  qrySaysNull
                } else// y != null constraint
                  if (!qrySaysNull) {
                    qry.removeLocalConstraint(e)
                    // add y -> ptY constraint to express that y != null
                    getPt(e.src.key, hg) match {
                      case rgn if rgn.isEmpty =>
                        if (Options.PRINT_REFS) println("refuted by empty points-to set w/ null comparison!")
                        false
                      case rgn =>
                        qry.addLocalConstraint(PtEdge.make(e.src, ObjVar(rgn)))
                        true
                    }
                  } else {
                    if (Options.PRINT_REFS) println("refuted by nullness in conditional!")
                    false
                  }
              } else {
                val zLPK = Var.makeLPK(useNum, n, hm)
                if (Pure.isEqualityOp(op)) {
                  if (stringConst) qry.addPureConstraint(Pure.makeEqConstraint(p, Pure.makePureVal(tbl, useNum)))
                  else {
                    // we have y -> p from constraints and conditional y == z, so z points to whatever y does
                    qry.addLocalConstraint(PtEdge.make(zLPK, p)) // add z -> p constraint
                    true
                  }
                } else {
                  // we have y -> p from constraints and conditional y != z, so cannot point to what y points to
                  if (qry.isNull(p)) { // then z cannot be null. add z -> pt(z) constraint
                    if (stringConst) true // z is definitely not null since it's a string constant
                    else {
                      val ptZ = getPt(zLPK, hg)
                      if (ptZ.isEmpty) false
                      else {
                        qry.addLocalConstraint(PtEdge.make(zLPK, ObjVar(ptZ)))
                        true
                      }
                    }
                  } else { // then z must be null. add z == null constraint
                    if (stringConst) false // z can't be null; it's a string constant
                    else {
                      qry.addLocalConstraint(PtEdge.make(zLPK, Qry.getNullVar(qry)))
                      true
                    }
                  }
                }
              }
          }
        }
        
        val (lpk0, lpk1) = (Var.makeLPK(use0, n, hm), Var.makeLPK(use1, n, hm)) // get LPK's for y and z
        (getConstraintEdge(lpk0, qry.localConstraints), getConstraintEdge(lpk1, qry.localConstraints)) match {
          case (Some(e0), Some(e1)) => handleObjComparison(e0.snk, e1.snk)           
          case (Some(e), None) => handleSingleObjComparison(e, use1)
          case (None, Some(e)) => handleSingleObjComparison(e, use0)
          case (None, None) =>  
            
            def addEqOrNeNullConstraint(useNum : Int, lpk : LocalPointerKey) : Boolean = {
              // useNum is either a null constant or a string constant
              assert(tbl.isNullConstant(useNum) || tbl.isStringConstant(useNum), 
                  s"useNum $useNum not a null constant or string constst. cond $cond  ir ${n.getIR()}")
              if (Pure.isEqualityOp(op) && tbl.isNullConstant(useNum)) { // var must be null
                val pNull = Qry.getNullVar(qry)
                qry.addLocalConstraint(PtEdge.make(lpk, pNull))
                true
              } else { // var must be non-null -- add constraint to say so
                val rgn = getPt(lpk, hg)
                if (rgn.isEmpty) { // lpk doesn't point to anything -- so it must be null  
                  val shouldRefute = refuteBasedOnEmptyPT(lpk, qry, n)
                  if (Options.PRINT_REFS && shouldRefute) println("Refuted by == null constraint!")
                  shouldRefute                  
                } else {
                  qry.addLocalConstraint(PtEdge.make(lpk, ObjVar(rgn)))
                  true
                }
              }
            } 
            
            // we already checked that at least one of the uses is not a constant
            if (use0Constant) addEqOrNeNullConstraint(use0, lpk1)  
            else if (use1Constant) addEqOrNeNullConstraint(use1, lpk0)  
            else { // neither is a constant
              val (rgn0, rgn1) = (getPt(lpk0, hg), getPt(lpk1, hg))
              if (Pure.isEqualityOp(op)) {
                val rgnInter = rgn0.intersect(rgn1)
                if (rgnInter.isEmpty) {
                  if (EMPTY_PT_WARNING && (rgn0.isEmpty || rgn1.isEmpty)) {
                    println(s"(2) Warning: returning null for v${lpk0.getValueNumber} and/or v${lpk1.getValueNumber} based on empty PT set")
                    // TODO: this is to guard against unsound refutations due to unsoundness in the points-to analysis,
                    // but is less good than actually fixing the points-to analysis
                    true
                  } else false
                  //false
                } else {
                  val interVar = ObjVar(rgnInter)
                  qry.addLocalConstraint(PtEdge.make(lpk0, interVar)) // add y -> interVar constraint
                  qry.addLocalConstraint(PtEdge.make(lpk1, interVar)) // add z -> interVar constraint
                  true
                }
              } else { // inequality comparison
                if (rgn0.isEmpty && rgn1.isEmpty) false // y and z needed to be different, but they're both null
                else {
                  def objVarOrNull(rgn : Set[InstanceKey]) : Val = 
                    if (rgn.isEmpty) {
                      println(s"(3) Warning: returning null for v${lpk0.getValueNumber} and/or v${lpk1.getValueNumber} based on empty PT set")
                      Qry.getNullVar(qry)
                    } else ObjVar(rgn)
                  // y and z need to point to different ObjVars            
                  qry.addLocalConstraint(PtEdge.make(lpk0, objVarOrNull(rgn0))) // add y -> interVar constraint
                  qry.addLocalConstraint(PtEdge.make(lpk1, objVarOrNull(rgn1))) // add z -> interVar constraint
                  true
                }
              }
            }
          case _ => sys.error("already have some ref to operands") // TODO: implement
        } 
      } else {
        val (lhs, rhs) = (getPureExprForLocal(use0, qry, n, hm), getPureExprForLocal(use1, qry, n, hm))
        // add lhsExpr op rhsExpr constraint
        qry.addPureConstraint(PureAtomicConstraint(lhs, op, rhs))
      }
    }
  } 
  
  def isDispatchFeasible(call : SSAInvokeInstruction, caller : CGNode, callee : CGNode, qry : Qry) : Boolean = {
    def receiverFeasible  : Boolean = call.isStatic || {
      val receiver = Var.makeLPK(call.getUse(0), caller, hm)
      qry.localConstraints.find(e => e.src.key == receiver) match {
        case Some(LocalPtEdge(_, o@ObjVar(rgnReceiver))) =>
          //val calleeClass = callee.getMethod().getDeclaringClass()
          //rgnReceiver.filter(i => cha.isAssignableFrom(i.getConcreteType(), calleeClass))
          // TODO: use context-sensitivity information and o vs callee information here
          true 
        case Some(LocalPtEdge(_, p@PureVar(_))) =>
          try {
            // make sure the receiver is non-null
            val res = qry.checkTmpPureConstraint(Pure.makeNeNullConstraint(p))
            if (!res && Options.PRINT_REFS) println("Refuted by null dispatch!")
            res
          } catch {
            case _ : UnknownSMTResult => true
          }
        case None => true // no constraint on receiver, assume feasible
      }
    }
    
    def retvalFeasible = !call.hasDef || {
      val callerRet = Var.makeLPK(call.getDef(), caller, hm)
      val calleeRet = Var.makeRVK(callee, hm)
      qry.localConstraints.find(e => e.src.key == callerRet) match {
        case Some(LocalPtEdge(_, retObj@ObjVar(_))) =>
          getPt(calleeRet, hg) match {
            case rgn if rgn.isEmpty =>              
              if (EMPTY_PT_WARNING) println(s"(4) Warning: returning null for $calleeRet based on empty PT set")
              false // callee only returns null, but we need it to return an ObjVar
            case rgn => // dispatch is onlyFeasible if rgn(retObj) \cap rgn(retObj) is non-empty 
              qry.intersectAndSubstitute(retObj, ObjVar(rgn), hg).isDefined 
          }      
        case _ => true // constraint is on a PureVal or there is no constraint. assume feasible     
      }
    }
    
    receiverFeasible && retvalFeasible    
  }
  
  /** @return false if call to Object.clone() could not have returned an object of the correct type, true otherwise */
  def handleCallToObjectClone(i : SSAInvokeInstruction, qry : Qry, node : CGNode) : Boolean = {
    getConstraintEdgeForDef(i, qry.localConstraints, node) match {
      case Some(e@LocalPtEdge(_, ObjVar(rgnX))) => // found edge x -> ptX
        qry.removeLocalConstraint(e)
        // resolve the receiver(s) of clone in our call stack/constraints and make sure each one is type-consistent with
        // the keys in rgnX
        // TODO: this is really ugly
        val callStkArr = qry.callStack.stack.toArray        
        !callStkArr.indices.exists(i => {
          val frame = callStkArr(i)
          frame.callInstr match {
            case Some(call) if (!call.isStatic() && call.getDeclaredTarget().getName().toString() == "clone") =>
              assert(i + 1 < callStkArr.length)
              val nextNode = callStkArr(i + 1).node // nextNode is the caller of call
              val receiverLPK = Var.makeLPK(call.getUse(0), nextNode, hm)
              val receiverTypes =
                if (receiverLPK.getValueNumber() == 1) Set(nextNode.getMethod().getDeclaringClass())
                else getPt(receiverLPK, qry.localConstraints, hg) match {
                  case Some((ObjVar(rgnReceiver), _)) => rgnReceiver.map(key => key.getConcreteType)
                  case None => Set.empty[IClass] // refuted by null dispatch
                }
              rgnX.exists(k =>
                receiverTypes.exists(receiverType => cha.isAssignableFrom(receiverType, k.getConcreteType)))
            case _ => false
        }})
      case Some(e@LocalPtEdge(_, p@PureVar(_))) =>
        qry.removeLocalConstraint(e)
        !qry.isNull(p)
      case _ => true // no relevant edge
    }
  }

  /** @return Some(calleeConstraints) if binding succeeded, None if binding caused refutation */
  def tryBindReturnValue(call : SSAInvokeInstruction, qry : Qry, caller : CGNode,
                         callee : CGNode) : Option[MSet[LocalPtEdge]] = {
    val calleeLocalConstraints = Util.makeSet[LocalPtEdge]
    if (call.hasDef) // x = call m(a, b, ...)
      getConstraintEdgeForDef(call, qry.localConstraints, caller) match {
        case Some(edge) => // found return value in constraints
          qry.removeLocalConstraint(edge) // remove x -> A constraint
          // add ret_callee -> A constraint
          calleeLocalConstraints += PtEdge.make(Var.makeReturnVar(callee, hm), edge.snk)
        case None => () // return value not in constraints, no need to do anything
      }

    Some(calleeLocalConstraints)
  }
  
  /** perform parameter binding and call stack manipulation associated with making a call to @param callee from
    * @param caller via the instruction @param call */
  def enterCallee(call : SSAInvokeInstruction, qry : Qry, caller : CGNode, callee : CGNode) : Boolean =
    tryBindReturnValue(call, qry, caller, callee) match {
      case Some(calleeLocalConstraints) =>
        val tbl = caller.getIR().getSymbolTable()
        // TODO: refute based on null dispatch-- or should this be done elsewhere?
        assert(call.isStatic() || !tbl.isNullConstant(call.getUse(0)))

        // TODO: add contextual constraints if we don't already have a constraint on the receiver
        // bind actuals of caller to formals of callee: add constraints m-1 -> a, m-2 -> b, etc.
        for (i <- 0 to call.getNumberOfUses - 1) {
          val (actualNum, formalNum) = (call.getUse(i), i + 1)
          val formalLPK = Var.makeLPK(formalNum, callee, hm)
          if (tbl.isConstant(actualNum)) { // actual is a constant c--we should bind it
            val paramType = callee.getMethod().getParameterType(i)
            val pureVar = Pure.makePureVar(paramType)
            // add m-i -> p-? constraint
            calleeLocalConstraints += PtEdge.make(formalLPK, pureVar)
            // add p-? == c pure constraint
            qry.addPureConstraint(Pure.makeEqConstraint(pureVar, Pure.makePureVal(tbl, actualNum)))
          } else getConstraintEdge(Var.makeLPK(actualNum, caller, hm), qry.localConstraints) match {
            case Some(LocalPtEdge(_, actualVar@ObjVar(_))) => // bind formalLPK to actualVar \cap interVar
              getPt(formalLPK, hg) match {
                case rgn if rgn.isEmpty => return false // refuted by null parameter when we needed actualVar
                case rgn => qry.intersectAndSubstitute(actualVar, rgn, hg) match {
                  case Some(interVar) => calleeLocalConstraints += PtEdge.make(formalLPK, interVar)
                  case None => return false
                }
              }
            case Some(LocalPtEdge(_, p@PureVar(_))) => // TODO: check for null/non-null here?
              calleeLocalConstraints += PtEdge.make(formalLPK, p)
            case None =>
              //if (!call.isStatic() && formalNum == 1) {
                // special case: it's sound to bind the receiver to its pts-to value since we know it can't be null
                // (else we'd have null dispatch) BUT, we'd have to consider aliasing case splits, which we don't
                // necessarily want to do
                // calleeLocalConstraints += PtEdge.make(formalVar, ObjVar(getPt(Var.makeLPK(actualNum, caller, hm), hg)))
              //} // else, don't know anything about the value of this argument; don't bind it
          }
        }

        qry.callStack.push(CallStackFrame.make(callee, calleeLocalConstraints, call))
        true
      case None => false // refuted by return value binding
    }
  
  // TODO: flush unused pure constraints
  def returnToCallerNormal(qry : Qry) : Boolean = {
    require(qry.callStack.size > 1, "Call stack should have > 1 frame, has " + qry.callStack.size)
    val calleeFrame = qry.callStack.pop
    val callInstr = calleeFrame.callInstr match {
      case Some(callInstr) => callInstr
      case other => sys.error("Expecting invoke instr as part of frame " + calleeFrame + "; got nothing")
    }

    bindFormalsToActuals(qry, callInstr, qry.node, calleeFrame.node, qry.localConstraints, calleeFrame.localConstraints)        
  }
  
  // TODO: flush unused pure constraints
  /** return from @param qry with empty call stack to @param caller */
  def returnToCallerContextFree(call : SSAInvokeInstruction, qry : Qry, caller : CGNode, callBlk : ISSABasicBlock,
                                callLine : Int) : Boolean = {
    require(qry.callStack.size == 1, "Call stack should have one frame, has " + qry.callStack.size)
    // TODO: need to do anything with return value here?
    val callerLocalConstraints = Util.makeSet[LocalPtEdge]
    val calleeFrame = qry.callStack.pop
    qry.callStack.push(new CallStackFrame(caller, callerLocalConstraints, callBlk, callLine)) // add the new stack frame
    val calleeConstraints = calleeFrame.localConstraints
    
    /*
    // add this -> pt(this) constraint. this may involve performing a case split
    if (!call.isStatic()) {
      val thisLPK = Var.makeLPK(1, callee, hm)      
      getPt(thisLPK, calleeConstraints, hg) match {
        case Some((thisVar, thisEdge)) => // add this -> pt(this) edge if applicable
          if (!thisEdge.isDefined) {
            qry.getAllObjVars.find(o => !o.rgn.intersect(thisVar.rgn).isEmpty) match {
              case Some(o) => sys.error("got possible aliasing via " + o + "! need to do case split")
              case None => // no aliasing to consider; just add the constraint 
                calleeConstraints += PtEdge.make(thisLPK, thisVar)
            }
          }
        case None => return false // this -> null, refute
      }     
    }*/
    
    bindFormalsToActuals(qry, call, caller, calleeFrame.node, callerLocalConstraints, calleeConstraints)    
  }     
  
  /** bind formals of callee to actuals of caller */
  private def bindFormalsToActuals(qry : Qry, call : SSAInvokeInstruction, caller : CGNode, callee : CGNode, 
                                   callerConstraints : MSet[LocalPtEdge],
                                   calleeConstraints : MSet[LocalPtEdge]) : Boolean = {
    if (!call.isStatic()) {
      val thisLPK = Var.makeLPK(1, callee, hm)
      
      def handleNoEdgeCase() : Boolean = getPt(thisLPK, hg) match {
        case rgn if rgn.isEmpty => false // this -> null, refute
        case rgn => 
          val thisVar = ObjVar(rgn)
          qry.getAllObjVars.find(o => !o.rgn.intersect(thisVar.rgn).isEmpty) match {
            case Some(o) => () 
              // possible aliasing -- do nothing. this is sound but not precise
              // TODO: we could case split all on all possible alias relationships instead
            case None => // no aliasing to consider; just add the constraint 
              calleeConstraints += PtEdge.make(thisLPK, thisVar)
          }
          true
      }
      
      getConstraintEdge(thisLPK, calleeConstraints) match {
        case Some(LocalPtEdge(_, thisVar@ObjVar(_))) => List(qry)
        case Some(e@LocalPtEdge(_, p@PureVar(_))) => 
          if (qry.isNull(p)) return false // this -> null, refute
          else {
            // get the points-to set of this and add edge this -> pt(this)
            qry.removeLocalConstraint(e)
            if (!handleNoEdgeCase) return false
          }
        case None => if (!handleNoEdgeCase) return false        
      }
    }
      
      /*getPt(thisLPK, calleeConstraints, hg) match {
        case Some((thisVar, thisEdge)) => // add this -> pt(this) edge if applicable
          if (!thisEdge.isDefined) {
            qry.getAllObjVars.find(o => !o.rgn.intersect(thisVar.rgn).isEmpty) match {
              case Some(o) => () // possible aliasing -- do nothing 
              case None => // no aliasing to consider; just add the constraint 
                calleeConstraints += PtEdge.make(thisLPK, thisVar)
            }
          } else List(qry)
        case None => Nil // this -> null, refute
      }     
    } else List(qry)*/
    
    val thisVar = Var.makeThisVar(callee, hm)
    val thisPT = Qry.getPT[LocalVar,ObjVar](thisVar, calleeConstraints)  
    
    // initialize instance fields to default values if callee was a constructor, bind formals to actuals if default value
    // initialization does not result in a refutation
    (!callee.getMethod().isInit() || initializeInstanceFieldsToDefaultValues(qry, callee, thisPT)) && {     
      val tbl = caller.getIR().getSymbolTable

      // TODO: refute based on contextual constraints on caller
      assert(call.isStatic() || !tbl.isNullConstant(call.getUse(0))) // TODO: refute based on null dispatch
      for (i <- 0 to callee.getMethod().getNumberOfParameters() - 1) { // TODO: rewrite as forall to make clearer?
        getConstraintEdge(Var.makeLPK(i + 1, callee, hm), calleeConstraints) match {
          case Some(edge) =>
            val callUse = call.getUse(i) 
            edge.snk match {            
              case formalObj@ObjVar(rgn) =>                
                // if callUse is a string constant, rgn should just contain a constant string key
                if (DEBUG) assert(!tbl.isStringConstant(callUse) || rgn.size == 1)                  
                if (tbl.isNullConstant(callUse)) {
                  if (Options.PRINT_REFS) println("Refuted by param binding to null")
                  return false
                } else {
                  val actual = Var.makeLPK(callUse, caller, hm)                            
                  getPtVal(actual, callerConstraints, hg) match {
                    case (ptActual@ObjVar(rgnActual), actualEdge) =>
                      val rgnInter = rgnActual.intersect(rgn) // do pt(actual) \cap pt(formal)
                      if (rgnInter.isEmpty) {               
                        if (Options.PRINT_REFS) println("Refuted by from constraints (parameter binding)!")
                        return false
                      } else {
                        val interVar = ObjVar(rgnInter)   
                        if (!qry.substitute(interVar, formalObj, hg)) return false
                        else if (actualEdge.isDefined) {
                          if (!qry.substitute(interVar, ptActual, hg)) return false
                        } else if (!tbl.isStringConstant(callUse)) qry.addLocalConstraint(LocalPtEdge(LocalVar(actual), interVar))
                        // if callUse is a string constant, this local edge has already been consumed
                        // else, everything is fine
                        //else if (!tbl.isStringConstant(callUse)) qry.addLocalConstraint(LocalPtEdge(LocalVar(actual), interVar))
                      } 
                    case (p@PureVar(_), actualEdge) =>
                      assert(!tbl.isConstant(callUse), "Have const " + actual + " ir " + caller.getIR())
                      if (qry.isNull(p)) return false // actual -> null, but we needed it to point to formalObj
                      else if (!actualEdge.isDefined) qry.addLocalConstraint(PtEdge.make(actual, formalObj))
                  }                    
                }
              case p@PureVar(_) =>                 
                val pureExpr = getOrCreatePureExprForUse(callUse, caller, qry)
                if (!qry.addPureConstraint(Pure.makeEqConstraint(p, pureExpr))) return false // refuted
            } 
          case None => () // this formal doesn't matter for our query
        }      
      }
      true
    }
  }
  
  private def getOrCreatePureExprForUse(useNum : Int, n : CGNode, qry : Qry) : PureExpr = {
    val tbl = n.getIR().getSymbolTable()
    if (tbl.isConstant(useNum)) Pure.makePureVal(tbl, useNum) 
    else {
      val lpk = Var.makeLPK(useNum, n, hm) 
      val (v, edge) = getPtVal(lpk, qry.localConstraints, hg)
      v match {
        case p@PureVar(_) => 
          if (!edge.isDefined) qry.addLocalConstraint(PtEdge.make(lpk, p))
          p
        case ObjVar(rgn) => // string constant case
          assert(!edge.isDefined) // TODO: add edge here?
          /*if (DEBUG) {
            assert(rgn.size == 1, "Expecting region of size 1, but size is " + rgn.size)
            rgn.head match {
              case k : ConcreteTypeKey => 
                assert(k.getType().getReference() == TypeReference.JavaLangString)
              case k => sys.error("Unexpected instance key " + k)
            }
          }*/
          Pure.NON_NULL
      }
    }
  }
  
  private def getCaseSplitList(edge : HeapPtEdge, xUse : Int, qry : Qry, n : CGNode) : List[Qry] = edge.src match {
    case xVar@ObjVar(rgn) => // have x -> A, A.f -> B
      val x = Var.makeLPK(xUse, n, hm)
      //val (ptX, xEdge) = getPt(x, qry.localConstraints, hg) 
      getPt(x, qry.localConstraints, hg) match {
        case Some((ptX, xEdge)) =>
          // do pt(x) \cap rgn(A)
          val xInter = ptX.rgn.intersect(rgn)
          if (xInter.isEmpty) Nil 
          else {
            val interVar = ObjVar(xInter)
            if (!xEdge.isDefined) { // no edge x -> ..., need to do a case split 
              val caseSplit = qry.clone
              qry.removeHeapConstraint(edge) 
              qry.addLocalConstraint(PtEdge.make(x, interVar)) // add x -> xInter edge for "consumed" case
              val res = qry.substitute(interVar, xVar, hg)
              assert(res)
              // add x -> pt(x) edge for "not consumed" case
              // implicitly, this says x points to some object different than A
              caseSplit.addLocalConstraint(PtEdge.make(x, ptX)) 
              List(caseSplit)
            } else { // have xEdge, no need to do a case split (would be immediately refuted by simultaneous pts-to on x)
              qry.removeHeapConstraint(edge) // need to do this before substitution, otherwise edge will change
              // substitute a new obj with region pt(x) \cap rgn(A) for A. No need to do this for ptX since it is the same
              // as xVar
              if (DEBUG) assert(ptX == xVar)
              val res = qry.substitute(interVar, xVar, hg) 
              assert(res)
              Nil
            }
          }
        case None => Nil // x -> null, so A.f would throw an exception
      }
      
    case _ => // static var; x is a class, not an instance. nothing interesting to do (no need for case split)
      qry.removeHeapConstraint(edge) 
      Nil    
  }  
  
  private def doAliasingCaseSplit(qry : Qry, xEdge : Option[LocalPtEdge], yVar : LocalVar, 
                                   ptY : ObjVar) : List[(Qry, ObjVar, Option[LocalPtEdge])] = {
    val notAliasedCase = qry.clone
    val maybeAliased = notAliasedCase.getAllObjVars
    val splits = maybeAliased.foldLeft (List((notAliasedCase, ptY, xEdge))) ((l, v) => {
      val rgnInter = ptY.rgn.intersect(v.rgn)
      if (rgnInter.isEmpty) l
      else {
        //println("Maybe aliased: " + v + " and " + ptY)
        val newQry = qry.clone
        val interVar = ObjVar(rgnInter)
        newQry.addLocalConstraint(LocalPtEdge(yVar, interVar))
        if (newQry.substitute(interVar, v, hg)) {
          val newXEdge = xEdge match {
            case old@Some(xEdge) => if (xEdge.snk == v) Some(LocalPtEdge(xEdge.src, interVar)) else old
            case None => xEdge
          }
          (newQry, interVar, newXEdge) :: l
        } else l
      }
    })
    // add local constraint for the "not aliased" case
    notAliasedCase.addLocalConstraint(PtEdge.make(yVar, ptY))
    splits
  }
  
  def getArrayIndexVar(s : SSAArrayReferenceInstruction, qry : Qry) = if (Options.INDEX_SENSITIVITY) {
    val n = qry.node
    // lookup i in constraints or create a fresh PureVar to represent i if it's not found
    val tbl = n.getIR().getSymbolTable()
    val indexUse = s.getIndex()
    val iLPK = Var.makeLPK(indexUse, n, hm)        
    getPtVal(iLPK, qry.localConstraints, hg) match {
      case (p@PureVar(_), _) =>
        if (tbl.isConstant(indexUse)) {
          val res = qry.addPureConstraint(Pure.makeEqConstraint(p, Pure.makePureVal(tbl, indexUse)))
          assert(res, s"Got refutation while adding equality to pure constraint: query $qry IR ${n.getIR}")
        } else // add edge i -> p 
          qry.addLocalConstraint(PtEdge.make(iLPK, p))
        Some(p)
      case o => sys.error("Expected PureVar, got " + o)
    }
  } else None // not index-sensitive
  
  
  def getRelevantArrayEdges(qry : Qry, arrRef : ObjVar, indexVar : Option[PureVar]) : (List[ArrayPtEdge], Boolean) = {
    // collect all edges in our constraints of the form A[i] -> ptYi 
    var mustEq = false
    (qry.heapConstraints.foldLeft (List.empty[ArrayPtEdge]) ((l, e) => 
    if (mustEq) l else e match {
      case e@ArrayPtEdge(src, fld, snk) if src == arrRef =>
        if (!Options.INDEX_SENSITIVITY) e :: l
        else if (Qry.indicesDefinitelyEqual(qry, fld, indexVar.get)) {
          mustEq = true
          List(e)
        } else if (Qry.indicesPossiblyEqual(qry, fld, indexVar.get)) e :: l 
        else l
      case _ => l
    }), mustEq)   
  }
                                         
  def execute(s : SSAInstruction, qry : Qry, n : CGNode) : List[Qry] = s match {
    case s : SSAPutInstruction => // x.f = y
      def processPut(edge : Option[HeapPtEdge], qry : Qry, l : List[Qry] = Nil) : List[Qry] = edge match {
        case Some(edge) => edge.src match { // have edge A.f -> B
          case xVar@ObjVar(rgn) => // have x -> A, A.f -> B
            val x = Var.makeLPK(s.getRef(), n, hm)
            getPtVal(x, qry.localConstraints, hg) match {
              case (ptX@ObjVar(_), xEdge) =>
                // do pt(x) \cap rgn(A)
                val xInter = ptX.rgn.intersect(rgn)
                if (xInter.isEmpty) return l
                qry.removeHeapConstraint(edge) 
                val interVar = ObjVar(xInter)
                if (!xEdge.isDefined) { // no edge x -> ...
                  qry.addLocalConstraint(PtEdge.make(x, interVar)) // add x -> xInter edge for "consumed" case
                } else { // have xEdge, no need to do a case split (would be immediately refuted by simultaneous pts-to on x)
                  if (!qry.substitute(interVar, xVar, hg)) return l// substitute a new obj with region pt(x) \cap rgn(A) for A 
                }
              case (pureX@PureVar(_), xEdge) =>
                assert(qry.isNull(pureX), "Expected null pure var, but got non-null pure var")
                return l // refuted; x == null, so x.f = y would throw an exception
            }      
            
          case _ => // static var; x is a class, not an instance. nothing interesting to do (no need for case split)
            qry.removeHeapConstraint(edge)       
          }

          val y = Var.makeLPK(s.getVal(), n, hm)                 
          edge.snk match {
            case ptB@ObjVar(rgn) => 
              if (!n.getIR().getSymbolTable().isNullConstant(s.getVal())) { // TODO: deal with nulls correctly
              
                def handleObjY(ptY : ObjVar, yEdge : Option[LocalPtEdge]) : List[Qry] = {
                  val yInter = ptY.rgn.intersect(rgn)
                  if (yInter.isEmpty) {
                    if (Options.PRINT_REFS) println("Refuted by simultaneous points-to on y in put x.f = y")
                    l
                  } else {
                    val yInterVar = ObjVar(yInter)
                    if (!qry.substitute(yInterVar, ptB, hg)) l // substitute a new obj with region pt(y) \cap rgn(B) for B
                    // add y -> interVar constraint, if it wasn't already added by substitution
                    else if (!yEdge.isDefined) {
                      qry.addLocalConstraint(PtEdge.make(y, yInterVar))                     
                      if (!qry.substitute(yInterVar, ptY, hg)) l
                      else qry :: l
                    } else qry :: l
                  }
                }
                
                def handleObjYOrRefute : List[Qry] = getPt(y, hg) match {
                  case rgnY if rgnY.isEmpty => l // refuted. y -> null, but x.f doesn't
                  case rgnY => handleObjY(ObjVar(rgnY), None)
                }
                
                getConstraintEdge(y, qry.localConstraints) match {
                  case Some(yEdge@LocalPtEdge(_, ptY@ObjVar(yRgn))) => handleObjY(ptY, Some(yEdge))
                  case Some(yEdge@LocalPtEdge(_, p@PureVar(_))) =>      
                    if (qry.isNull(p)) l
                    else handleObjYOrRefute
                  case None => handleObjYOrRefute
                }          
              } else {
                if (Options.PRINT_REFS) println("Refuted by assignment to null!")
                l
              }

            case p@PureVar(_) => 
              getConstraintEdge(y, qry.localConstraints) match {
                case Some(LocalPtEdge(y, ptY@ObjVar(rgnY))) =>
                  if (!qry.isNull(p)) qry :: l
                  else l
                case Some(LocalPtEdge(y, pureY@PureVar(_))) =>
                  if (qry.addPureConstraint(Pure.makeEqConstraint(p, pureY))) qry :: l
                  else l
                case None =>
                  // getPureExprForLocalInternal adds a y -> constraint
                  if (qry.addPureConstraint(Pure.makeEqConstraint(p, getPureExprForLocalInternal(y, qry)))) qry :: l
                  else l
              }         
            case other => sys.error("bad snk for edge " + edge)
          }
        case None => qry :: l // no matching edge
      }
      
      val fld = cha.resolveField(s.getDeclaredField())
      if (s.isStatic()) processPut(getConstraintEdgeForStaticFld(fld, qry.heapConstraints, hm), qry)
      else {
        val x = Var.makeLPK(s.getRef(), n, hm)
        getConstraintEdge(x, qry.localConstraints) match {
          case Some(LocalPtEdge(_, ptX@ObjVar(_))) => // we have an edge x -> A, so we know what object this instruction writes to
            processPut(getConstraintPt(ptX, fld, qry.heapConstraints), qry)
          case Some(xEdge@LocalPtEdge(_, pureX@PureVar(_))) =>
            if (qry.isNull(pureX)) Nil
            else getPt(x, hg) match {
              case rgn if rgn.isEmpty => Nil // x -> null, so write x.f = y would throw exception                   
              case rgn => 
                val ptX = ObjVar(rgn)
                qry.removeLocalConstraint(xEdge)
                qry.addLocalConstraint(PtEdge.make(x, ptX))
                processPut(getConstraintPt(ptX, fld, qry.heapConstraints), qry)
            }
          case None => // no edge x -> A. need to consider each edge of the form A.f -> B that may be consumed by this instruction                
            getPt(x, hg) match {
              case rgn if rgn.isEmpty => Nil // x -> null, so write x.f = y would throw exception
              case rgn => 
                val ptX = ObjVar(rgn)
                getConstraintPt(ptX.rgn, fld, qry.heapConstraints) match {
                  case Some(edges) => 
                    val cases = edges.foldLeft (List.empty[Qry]) ((l, e) => processPut(Some(e), qry.clone, l))
                    //if (!cases.isEmpty) {
                      // add "edge not consumed" case by adding x -> ptX constraint
                      qry.addLocalConstraint(PtEdge.make(x, ptX))
                      qry :: cases
                    //} else cases
                  case None => List(qry) // no edges that can be produced by this instruction
                }
            }
        }
      }

    case s : SSAArrayStoreInstruction => // x[i] = y
      
      def handleArrEdge(qry : Qry, arrEdge : ArrayPtEdge, l : List[Qry]) : List[Qry] = {
        val yUse = s.getValue
        val y = Var.makeLPK(yUse, n, hm)  
        arrEdge match { // edge ptX[i] -> ptYi
          case arrEdge@ArrayPtEdge(ptX@ObjVar(rgnX), _, ObjVar(rgnPtYi)) => 
            
            def handleArrEdgeInternal(ptY : ObjVar, yEdge : Option[LocalPtEdge]) : List[Qry] = {
              // do pt(y) \cap rgn(B)
              val yInter = ptY.rgn.intersect(rgnPtYi)
              if (yInter.isEmpty) {
                if (Options.PRINT_REFS) println("refuted by simultaneous points-to on y in x[i] = y")
                l
              } else {
                qry.removeHeapConstraint(arrEdge)
                val yInterVar = ObjVar(yInter)
                if (!qry.substitute(yInterVar, ptY, hg)) l // substitute a new obj with region pt(y) \cap rgn(B) for B
                else {
                  // add y -> interVar constraint, if it wasn't already added by substitution                
                  if (!yEdge.isDefined) qry.addLocalConstraint(PtEdge.make(y, yInterVar))                     
                  qry :: l
                }
              }
            }          
            
            def handleOrRefuteIfNull = getPt(y, hg) match {
              case rgn if rgn.isEmpty => l // pt(y) === null, but ObjVar(rgnPtYi) isn't. refuted
              case rgn => handleArrEdgeInternal(ObjVar(rgn), None)
            }
            
            getConstraintEdge(y, qry.localConstraints) match {
              case Some(yEdge@LocalPtEdge(_, ptY@ObjVar(rgnY))) => handleArrEdgeInternal(ptY, Some(yEdge))                
              case Some(LocalPtEdge(_, yVar@PureVar(_))) => if (qry.isNull(yVar)) l else handleOrRefuteIfNull
              case None => handleOrRefuteIfNull
            }
       
          case arrEdge@ArrayPtEdge(ptX@ObjVar(rgnX), _, p@PureVar(_)) =>
            qry.removeHeapConstraint(arrEdge)
            getConstraintEdge(y, qry.localConstraints) match {
              case Some(LocalPtEdge(_, yVar@PureVar(_))) =>
                if (qry.addPureConstraint(Pure.makeEqConstraint(yVar, p))) qry :: l
                else l // refuted
              case None =>
                val tbl = n.getIR().getSymbolTable()
                if (tbl.isConstant(yUse)) {
                  if (qry.addPureConstraint(Pure.makeEqConstraint(p, Pure.makePureVal(tbl, yUse)))) qry :: l
                  else l
                } else {
                  qry.addLocalConstraint(PtEdge.make(y, p)) // add y -> p constraint
                  qry :: l
                }
              case e => sys.error("unexpected edge " + e)
            }                
        }   
      }
      
      def handleArrayStoreInternal(splits : List[(Qry, ObjVar, Unit => Unit)]) : List[Qry] =                
        splits.foldLeft (List.empty[Qry]) ((l, qryTrio) => {
          val (qry, arrRef, addNonAliasingConstraintsCB) = qryTrio
          val indexVar = getArrayIndexVar(s, qry)
          val (arrConstraints, mustEq) = getRelevantArrayEdges(qry, arrRef, indexVar)
          if (arrConstraints.isEmpty) {
            if (DEBUG) assert(splits.size == 1, s"have ${splits.size} splits") // TODO: otherwise we may be creating unecessary case splits
            List(qry)
          } else {
            addNonAliasingConstraintsCB() // invoke callback to add non-aliasing constraints
            if (mustEq) handleArrEdge(qry, arrConstraints.head, l)
            else // may eq case, so must add qry to l to account for possibility that index was not written to 
              arrConstraints.foldLeft (qry :: l) ((l, e) => handleArrEdge(qry.clone, e, l))
          }
        })
            
      val x = Var.makeLPK(s.getArrayRef, n, hm)
      getConstraintEdge(x, qry.localConstraints) match {
        case Some(LocalPtEdge(_, p@PureVar(_))) =>
          assert(qry.isNull(p), "expected null " + p)
          Nil // refuted by null read
        case Some(LocalPtEdge(_, ptX@ObjVar(_))) => 
          val caseSplits = qry.heapConstraints.foldLeft (List.empty[(Qry,ObjVar, Unit => Unit)]) ((l, e) => e match {
            case e@ArrayPtEdge(o@ObjVar(rgn), ArrayFld(_, _, _), _) if o == ptX => (qry.clone, ptX, (x : Unit) => ()) :: l
            case _ => l
          })
          if (caseSplits.isEmpty) List(qry)
          else handleArrayStoreInternal(caseSplits)
        case None => // no edge x -> ptX, add aliasing case splits
          getPt(x, hg) match {
            case rgn if rgn.isEmpty => Nil // x -> null, so x[i] = y would throw an exception
            case rgn =>
              val ptX = ObjVar(rgn)
              val xLoc = LocalVar(x)
              val caseSplits = qry.heapConstraints.foldLeft (List.empty[(Qry,ObjVar,Unit => Unit)]) ((l, e) => e match {
                case e@ArrayPtEdge(o@ObjVar(rgn), fld, _) =>              
                  val rgnInter = rgn.intersect(ptX.rgn)
                  if (rgnInter.isEmpty) l
                  else {
                    val interVar = ObjVar(rgnInter)
                    val newQry = qry.clone
                    if (!newQry.substitute(interVar, o, hg)) l
                    else {
                      val addNonAliasingConstraintsCB = (x : Unit) => Var.markCantAlias(ptX, o)
                      newQry.addLocalConstraint(LocalPtEdge(xLoc, interVar))
                      // TODO: get the new array pt edge
                      (newQry, interVar, addNonAliasingConstraintsCB) :: l
                    }
                  }
                  
                case _ => l
              })
              if (caseSplits.isEmpty) List(qry) // no constraint can be consumed by this instruction
              else {
                // add "edge not consumed" case split
                val notConsumedQry = qry.clone
                notConsumedQry.addLocalConstraint(LocalPtEdge(xLoc, ptX))
                notConsumedQry :: handleArrayStoreInternal(caseSplits)
              }
          }
          
      }     
      
    case s : SSAGetInstruction => // x = y.f
      val iFld = cha.resolveField(s.getDeclaredField())            
      getConstraintEdgeForDef(s, qry.localConstraints, n) match {
        case Some(xEdge) =>
          def processGet(qry : Qry, ptY : ObjVar, fld : InstanceFld, xEdge : LocalPtEdge) : Boolean = {                        
            getConstraintPt(ptY, iFld, qry.heapConstraints) match {
              case Some(e@ObjPtEdge(_, _, ptYf@ObjVar(rgnA))) => // found edge ptY.f -> A
                processGetInternal(qry, ptY, fld, ptYf, xEdge, Some(e))
              case Some(e@ObjPtEdge(src, f, p@PureVar(_))) => // found edge ptY.f -> p
                xEdge.snk match {
                  case snk@PureVar(_) =>
                    qry.addPureConstraint(Pure.makeEqConstraint(p, snk))
                  case o@ObjVar(_) => 
                    val res = qry.addPureConstraint(Pure.makeNeNullConstraint(p))
                    if (res) {
                      qry.removeHeapConstraint(e)
                      qry.addHeapConstraint(ObjPtEdge(src, f, o))
                    }
                    res
                }                
              case None => // no edge ptY.f -> ..., need to lookup pt(y.f) in heap graph
                if (iFld.getFieldTypeReference().isPrimitiveType())
                  // add ptY.f -> c constraint
                  qry.addHeapConstraint(PtEdge.make(ptY, fld, xEdge.snk))
                else {
                  val ptYf = getPt(ptY, iFld, hg) match {
                    case rgn if rgn.isEmpty => Qry.getNullVar(qry)
                    case rgn => ObjVar(rgn)
                  }
                  processGetInternal(qry, ptY, fld, ptYf, xEdge, None)
                }
            }
          }                    
                                      
          def processGetInternal(qry : Qry, ptY : HeapVar, fld : Fld, ptYf : Val, xEdge : LocalPtEdge, yfEdge : Option[HeapPtEdge]) : Boolean =
            (xEdge.snk, ptYf) match {
              case (ptX@ObjVar(rgnX), ptYf@ObjVar(rgnPtYf)) => 
                qry.intersectAndSubstitute(ptX, ptYf, hg) match {
                  case Some(interVar) => if (!yfEdge.isDefined) {
                      assert(interVar != ptX)
                      if (ptY == ptX || ptY == ptYf) qry.addHeapConstraint(PtEdge.make(interVar, fld, interVar))
                      else qry.addHeapConstraint(PtEdge.make(ptY, fld, interVar))
                    } else true
                    //yfEdge.isDefined || interVar == ptX || qry.addHeapConstraint(PtEdge.make(ptY, fld, interVar))
                  case None => false // refuted
                }                               
              case (pureX@PureVar(_), p@PureVar(_)) => yfEdge match {
                case Some(yfEdge) => // already have y.f -> c constraint. add c == p constraint
                  qry.addPureConstraint(Pure.makeEqConstraint(p, pureX))
                case None => // no yfEdge -- add y.f -> pureX constraint
                  qry.addHeapConstraint(PtEdge.make(ptY, fld, pureX))
              }  
              case (pureX@PureVar(_), ptYf@ObjVar(_)) => yfEdge match {
                case Some(yfEdge) => // already have y.f -> ptYf constraint
                  qry.addPureConstraint(Pure.makeNeNullConstraint(pureX))
                case None => // no edge -- add y.f -> pureX constraint
                  qry.addHeapConstraint(PtEdge.make(ptY, fld, pureX))                  
              }                
              case (ptX@ObjVar(_), p@PureVar(_)) => yfEdge match {
                case Some(yfEdge) => // already have y.f -> p constraint
                  qry.addPureConstraint(Pure.makeNeNullConstraint(p))
                case None => // no edge -- add y.f -> ptX constraint
                  qry.addHeapConstraint(PtEdge.make(ptY, fld, ptX))
              }
            }                     
          
          // need to do this before substitution
          qry.removeLocalConstraint(xEdge) // remove x -> ObjVar(xRgn) constraint
          if (iFld.isStatic()) { // x = C.f
            val ptY = ClassVar(iFld.getDeclaringClass())
            val (ptYf, yfEdge) = getPtS(iFld, qry.heapConstraints, hm, hg) match { // get pt(C.f)
              case Some(pair) => pair
              case None => 
                (Qry.getNullVar(qry), None)                
            }
            if (processGetInternal(qry, ptY, Fld.makeStaticFld(iFld, hm), ptYf, xEdge, yfEdge)) List(qry)
            else Nil
          } else {
            def processCaseSplits(caseSplits : List[(Qry, ObjVar, Option[LocalPtEdge])]) : List[Qry] = {
              val instanceFld = InstanceFld(iFld)
              caseSplits.foldLeft (List.empty[Qry]) ((l, qryTrio) => 
              if (processGet(qryTrio._1, qryTrio._2, instanceFld, qryTrio._3.get)) qryTrio._1 :: l else l)
            }
            
            val y = Var.makeLPK(s.getRef(), n, hm)
            getConstraintEdge(y, qry.localConstraints) match {
              case Some(e@LocalPtEdge(_, ptY@ObjVar(_))) =>
                processCaseSplits(List((qry, ptY, Some(xEdge))))
              case Some(LocalPtEdge(_, ptY@PureVar(_))) =>
                assert(qry.isNull(ptY), "expecting null, but got " + ptY)
                Nil // refuted by null read
              case None => // no edge y -> _. lookup pt(y.f) in the heap graph
                getPt(y, hg) match {
                  case rgn if rgn.isEmpty => Nil // refuted. y == null, so the read y.f would throw an exception
                  case rgn => processCaseSplits(doAliasingCaseSplit(qry, Some(xEdge), LocalVar(y), ObjVar(rgn))) 
                }
                                   
            }           
          }          
        case None => List(qry)
      }      
                   
    case s : SSAArrayLoadInstruction => // x = y[i]
      getConstraintEdgeForDef(s, qry.localConstraints, n) match {
        case Some(xEdge) => // found edge x -> ptX
          qry.removeLocalConstraint(xEdge)                                                         
          
          def handleArrayLoadInternal(splits : List[(Qry, ObjVar, Option[LocalPtEdge])]) =
            splits.foldLeft (List.empty[Qry]) ((l, qryTrio) => {
              val (qry, ptY) = (qryTrio._1, qryTrio._2)
              val indexVar = getArrayIndexVar(s, qry)
              val (arrConstraints, mustEq) = getRelevantArrayEdges(qry, ptY, indexVar)

              def processArrConstraint(e : ArrayPtEdge,
                                       l : List[Qry],
                                       anyArrConstraint : ArrayPtEdge = null) : List[Qry] = (e.snk, xEdge.snk) match {
                case (ptYi@ObjVar(rgnYi), ptX@ObjVar(rgnX)) =>                  
                  val rgnInter = rgnX.intersect(rgnYi) // do pt(x) \cap pt(y[i])
                  if (rgnInter.isEmpty) l
                  else {
                    val newQuery = qry.clone
                    val interVar = ObjVar(rgnInter)                                          
                    // if ptYi[i] -> A is not already in our constraints, add it
                    if ((e eq anyArrConstraint) && !newQuery.addHeapConstraint(PtEdge.make(e.src, e.fld, interVar))) l
                    else
                      if (newQuery.substitute(interVar, ptYi, hg) && newQuery.substitute(interVar, ptX, hg)) newQuery :: l
                      else l // refuted by infeasible substitution
                  }
                case (ptYi@ObjVar(_), pureX@PureVar(_)) =>
                  // e != anyArrConstraint check to account for the possibility that ptYi is a null value
                  if (qry.isNull(pureX) && e != anyArrConstraint) l // refuted
                  else {
                    // essentially, we have an x == null constraint. without index-sensitivity, there's no sense in
                    // adding a y[i] == null constraint since we can't ever prove that null won't be read from the array
                    qry.clone :: l
                  }
                case (pureYi@PureVar(_), ptX@ObjVar(_)) =>
                  if (qry.isNull(pureYi)) l // refuted
                  else {
                    // essentially, we have an x == null constraint. without index-sensitivity, there's no sense in
                    // adding a y[i] == null constraint since we can't ever prove that null won't be read from the array
                    qry.clone :: l
                  }
                case (pureYi@PureVar(_), pureX@PureVar(_)) =>
                  val newQuery = qry.clone
                  if (newQuery.addPureConstraint(Pure.makeEqConstraint(pureYi, pureX))) {
                    // if ptYi[i] -> A is not already in our constraints, add it
                    if ((e eq anyArrConstraint) && !newQuery.addHeapConstraint(e)) l
                    else newQuery :: l 
                  } else l
              }                
              
              if (mustEq) {
                assert (arrConstraints.size == 1)
                // read had to have come from arrConstraints.head
                processArrConstraint(arrConstraints.head, l)
              } else {
                // need to do case splits for each may eq edge AND consider the possibility that the read came from elsewhere 
                // get a pt constraint expressing that arr can point to anything in its points-to set (a "read from elsewhere" case split)
                val anyArrConstraint = getPtArr(ptY, indexVar, hg, hm, cha)
                (anyArrConstraint :: arrConstraints).foldLeft (l) ((l, e) => processArrConstraint(e, l, anyArrConstraint))
              }
            })
         
            
          val y = Var.makeLPK(s.getArrayRef(), n, hm)
          
          def handleUnknownY : List[Qry] = getPt(y, hg) match {
            case rgn if rgn.isEmpty => Nil
            case rgn => 
              // collect heap locs that may be the same as ptY
              val ptY = ObjVar(rgn)
              val splits = doAliasingCaseSplit(qry, Some(xEdge), LocalVar(y), ptY)
              handleArrayLoadInternal(splits)  
          }
          
          getConstraintEdge(y, qry.localConstraints) match {
            case Some(yEdge@LocalPtEdge(_, ptY@ObjVar(_))) => handleArrayLoadInternal(List((qry, ptY, Some(yEdge)))) // have edge y -> ptY              
            case Some(LocalPtEdge(_, p@PureVar(_))) => 
              if (qry.isNull(p)) Nil // y == null, so x = y[i] would throw an exception
              else handleUnknownY
            case None => handleUnknownY
          }
    
        case None => List(qry) // no edge x -> ...
      }
               
    case s : SSAArrayLengthInstruction => // x = y.length
      getConstraintEdgeForDef(s, qry.localConstraints, n) match {
        case Some(edge) => // found edge x -> v0         
          qry.removeLocalConstraint(edge)
          edge.snk match {
            case p@PureVar(_) =>
              val y = Var.makeLPK(s.getArrayRef(), n, hm)
              
              def handleObjY(ptY : ObjVar) : List[Qry] = {
                val rgnPtY = ptY.rgn
                val splitList = qry.heapConstraints.foldLeft (List.empty[Qry]) ((l, e) => e match {
                  case ObjPtEdge(ptY@ObjVar(rgn), fld, lengthPure@PureVar(_)) if Fld.isArrayLengthFld(fld) =>
                  val rgnInter = rgn.intersect(rgnPtY)
                  if (rgnInter.isEmpty) l
                  else {
                    val interVar = ObjVar(rgnInter)
                        // add case split
                        val newQry = qry.clone
                        if (newQry.substitute(interVar, ptY, hg)) {
                          newQry.addLocalConstraint(PtEdge.make(y, interVar))
                          if (newQry.addPureConstraint(Pure.makeEqConstraint(lengthPure, p))) newQry :: l
                          else l
                        } else l
                  }
                  case _ => l
                })
                val notConsumedCase = qry.clone
                notConsumedCase.addLocalConstraint(PtEdge.make(y, ptY))
                if (notConsumedCase.addHeapConstraint(PtEdge.make(ptY, Fld.ARRAY_LENGTH, p)) &&
                    // make it explicit that length is non-negative according to Java semantics
                    notConsumedCase.addPureConstraint(Pure.makeGeConstraint(p, IntVal(0)))) notConsumedCase :: splitList
                else splitList            
              }
              
              def handleObjYOrRefute : List[Qry] = getPt(y, hg) match {
                case rgnY if rgnY.isEmpty => Nil // refuted. y -> null, so y.length would throw an exception
                case rgnY => handleObjY(ObjVar(rgnY))
              }
              
              getConstraintEdge(y, qry.localConstraints) match {
                case Some(LocalPtEdge(_, ptY@ObjVar(rgnY))) => // look for ptY.length -> ... constraint 
                  qry.heapConstraints.find(e => e.src == ptY && Fld.isArrayLengthFld(e.fld)) match {
                    case Some(lengthEdge) => // found constraint ptY.length = q, add pure constraint p == q                     
                      if (qry.addPureConstraint(Pure.makeEqConstraint(p, getSnkAsPureVar(lengthEdge)))) List(qry)
                      else Nil // refuted
                    case None =>
                      if (qry.addHeapConstraint(PtEdge.make(ptY, Fld.ARRAY_LENGTH, p)) &&
                          // make it explicit that length is non-negative according to Java semantics
                          qry.addPureConstraint(Pure.makeGeConstraint(p, IntVal(0)))) List(qry)
                      else Nil
                  }
                case Some(LocalPtEdge(_, pureY@PureVar(_))) =>
                  if (qry.isNull(pureY)) Nil // refuted. y -> null, so y.length would throw an exception
                  else handleObjYOrRefute
                case None => handleObjYOrRefute                
              } 
            case _ => sys.error("Unexpected snk for edge " + edge)
          }
        case None => List(qry) // no matching edge found
      }  
      
    case _ => // not an instruction that can cause a case split. do regular execution 
      if (executeInternal(s, qry, n)) List(qry) else Nil
    //case s : SSAArrayStoreInstruction =>    
  }
  
  // TODO: use this to avoid boilerplate
  /*
  private def executeDefInstruction(s : SSAInstruction, qry : Qry, n : CGNode) : Boolean = {
    if (s.hasDef()) getConstraintPtForDef(s, qry.localConstraints, n) match {
      case (Some(edge)) => executeInternal(s, edge, qry, n)
      case None => true // no matching edge found
    } else sys.error("nonDef")
  }*/
  
  // TODO: this might be cleaner we define a partial function for each instruction that is only applied 
  // upon finding a matching edge in the constraints  
  protected def executeInternal(s : SSAInstruction, qry : Qry, n : CGNode) : Boolean = s match {
    case s : SSANewInstruction => // x = new_a T()      
      def processArrayConstraints(arr : ObjVar) : Boolean = !s.getNewSite().getDeclaredType().isArrayType() || {
        val tbl = n.getIR().getSymbolTable()
        val lengthUse = s.getUse(0)
        // get or create pure val corresponding to declared length in instruction
        val arrLengthVal = getOrCreatePureExprForUse(lengthUse, n, qry)
        // remove A.length -> v constraints and add v == pureVar constraints 

        // also, initialize all array elements to default values TODO: not sure this is sound without an x -> ... constraint?
        qry.heapConstraints.forall(e => e match {
          case e@ObjPtEdge(o@ObjVar(_), f@InstanceFld(_), p@PureVar(_)) if arr == o && Fld.isArrayLengthFld(f) =>
            val res = qry.addPureConstraint(Pure.makeEqConstraint(p, arrLengthVal))
            if (res) qry.removeHeapConstraint(e)
            res
          case e@ArrayPtEdge(o@ObjVar(_), _, snk) if arr == o => snk match {
            case p@PureVar(_) =>
              val res = qry.addPureConstraint(Pure.makeDefaultValConstraint(p))
              if (res) qry.removeHeapConstraint(e)
              res
            case ObjVar(_) =>
              if (Options.PRINT_REFS) println("Refuted by initialization of array vars to null!")
              false
          }            
          case _ => true
        })                    
      }
      
      getConstraintEdgeForDef(s, qry.localConstraints, n) match { // get pt(x)--should be just a!
        case Some(e@LocalPtEdge(_, ptX@ObjVar(rgn))) => // to consume this constraint, a \in rgn(ptX) must hold      
          if (rgn.contains(hm.getInstanceKeyForAllocation(n, s.getNewSite()))) {
            qry.removeLocalConstraint(e)
            // once we perform the allocation there should be no outstanding references to ptX anywhere in our constraints,
            // since it is impossible to reference a heap location before it is allocated
            if (processArrayConstraints(ptX)) {
              if (qry.getAllObjVars.contains(ptX)) {
                if (Options.PRINT_REFS) println("Refuted by outstanding reference to " + ptX + " after allocation")
                false
              } else true 
            } else false // refuted by array constraints  
          } else {
            if (Options.PRINT_REFS) println("Refuted by bad allocation!")
            false
          }  
        case Some(e@LocalPtEdge(_, pureX@PureVar(_))) =>
          if (qry.isNull(pureX)) false // refuted 
          else {
            qry.removeLocalConstraint(e)
            true
          }
        case None => true // no matching edge in localConstraints
      }    
      
    case s : SSAReturnInstruction => // return x
      getConstraintEdgeForRet(qry.localConstraints, n) match {
        case Some(edge) => // found edge ret_n -> A
          qry.removeLocalConstraint(edge) // remove ret_n -> A          
          val resultNum = s.getResult()
          val tbl = n.getIR().getSymbolTable          
          val x = Var.makeLPK(resultNum, n, hm)

          edge.snk match {
            case ptA@ObjVar(rgnA) =>
              if (tbl.isNullConstant(resultNum)) false // refuted by returning null
              else getConstraintEdge(x, qry.localConstraints) match {
                case Some(xEdge@LocalPtEdge(_, ptX@ObjVar(ptXRgn))) =>
                  val rgnInter = rgnA intersect ptXRgn // do A \cap pt(x)
                  if (rgnInter.isEmpty) false // refuted
                  else {
                    val interVar = ObjVar(rgnInter)
                    if (!qry.substitute(interVar, ptA, hg)) false
                    else if (!qry.substitute(interVar, ptX, hg)) false
                    else {
                      if (!tbl.isConstant(resultNum)) qry.addLocalConstraint(PtEdge.make(x, interVar)) // add edge x -> (A \cap pt(x))
                      true
                    }
                  }
                case Some(xEdge@LocalPtEdge(_, p@PureVar(_))) =>
                  if (qry.isNull(p)) false // refuted
                  else {
                    qry.removeLocalConstraint(xEdge)
                    if (!tbl.isConstant(resultNum)) qry.addLocalConstraint(PtEdge.make(x, ptA)) // add edge x -> (A \cap pt(x))
                    true
                  }
                  // TODO: check for null
                case None =>
                  val ptXRgn = getPt(x, hg)
                  val rgnInter = rgnA intersect ptXRgn
                  if (rgnInter.isEmpty) false // refuted
                  else {
                    val interVar = ObjVar(rgnInter)
                    if (!qry.substitute(interVar, ptA, hg)) false
                    else {
                      if (!tbl.isConstant(resultNum)) qry.addLocalConstraint(PtEdge.make(x, interVar))
                      true
                    }
                  }
              }
          
            case p@PureVar(_) =>
              if (tbl.isConstant(resultNum)) qry.addPureConstraint(Pure.makeEqConstraint(p, Pure.makePureVal(tbl, resultNum)))
              else getConstraintEdge(x, qry.localConstraints) match {
                case Some(LocalPtEdge(_, pureSnk@PureVar(_))) => // found existing x -> v edge. add p == v constraint  
                  qry.addPureConstraint(Pure.makeEqConstraint(p, pureSnk))
                case Some(LocalPtEdge(_, o@ObjVar(_))) =>
                  !qry.isNull(p) // if p is definitely null, refuted by null/non-null mismatch
                case None => 
                  qry.addLocalConstraint(PtEdge.make(x, p)) // add edge x -> p
                  true
              }
          }
        case None => true // no matching edge in localConstraints
      }
      
    case s : SSAInstanceofInstruction => // x = y instanceof T
      getConstraintEdgeForDef(s, qry.localConstraints, n) match {
        case Some(edge) => // found edge x -> v0
          qry.removeLocalConstraint(edge)
          edge.snk match {
            case p@PureVar(_) =>
              try {
                // find pure constraint(s) on p
                val negated = qry.checkTmpPureConstraint(Pure.makeEqBoolConstraint(p, false))

                // find y and filter it by the type of T
                val checkedType = cha.lookupClass(s.getCheckedType())
                val yLPK = Var.makeLPK(s.getRef(), n, hm)

                def handleYObj(ptY : ObjVar, yEdge : Option[LocalPtEdge]) : Boolean = {
                  val newRgn = ptY.rgn.filter(k => {
                    val assignable = cha.isAssignableFrom(checkedType, k.getConcreteType())
                    (assignable && !negated) || (!assignable && negated)
                  })

                  // record result of instanceof and do SAT check
                  if (!newRgn.isEmpty && qry.addPureConstraint(Pure.makeEqBoolConstraint(p, !negated))) {
                    // add newly constrained edge to points-to constraints
                    val newVar = ObjVar(newRgn)
                    if (yEdge.isDefined && !qry.substitute(newVar, ptY, hg)) false
                    else {
                      qry.addLocalConstraint(PtEdge.make(yLPK, newVar))
                      true
                    }
                  } else {
                    if (Options.PRINT_REFS) println("Refuted by instanceof check!")
                    false // refuted
                  }
                }

                def handleNoEdge() : Boolean = {
                  val ptY = getPt(yLPK, hg)
                  if (ptY.isEmpty) handleYNull
                  else handleYObj(ObjVar(ptY), None)
                }

                def handleYNull() : Boolean = { // x = null instanceof T
                val pNull = Qry.getNullVar(qry)
                  qry.addLocalConstraint(PtEdge.make(yLPK, pNull))
                  true
                }

                getConstraintEdge(yLPK, qry.localConstraints) match {
                  case Some(e@LocalPtEdge(_, ptY@ObjVar(_))) => handleYObj(ptY, Some(e))
                  case Some(e@LocalPtEdge(_, p@PureVar(_))) =>
                    if (qry.isNull(p)) true
                    else {
                      // edge says that y points-to some non-null value
                      // remove this edge and replace it with y's points-to set
                      qry.removeLocalConstraint(e)
                      handleNoEdge
                    }
                  case None =>
                    val ptY = getPt(yLPK, hg)
                    if (ptY.isEmpty) handleYNull
                    else handleYObj(ObjVar(ptY), None)
                }
              } catch {
                case e : UnknownSMTResult => true
              }
            case _ => sys.error("Unexpected snk for edge " + edge)
          }
        case None => true
      }
      
    case s : SSACheckCastInstruction => // x = (T) y

      val types = s.getDeclaredResultTypes()
      assert(types.length == 1) // in Java, this should be true
      val castType = cha.lookupClass(types(0))
      def filterByCastType(rgn : Set[InstanceKey]) =
        rgn.filter(k => cha.isAssignableFrom(castType, k.getConcreteType()))

      getConstraintEdgeForDef(s, qry.localConstraints, n) match {
        case Some(e@LocalPtEdge(_, ptX@ObjVar(xRgn))) => // found edge x -> A          
          qry.removeLocalConstraint(e)
          val y = Var.makeLPK(s.getVal(), n, hm)
          
          def handleObjY(ptY : ObjVar, yEdge : Option[LocalPtEdge]) : Boolean = {
            // TODO: implement option to add constraints from checking casts
            // filter ptY by cast type T; for each key k in ptY, keep only k's such that type(k) <: T
            val filteredYRgn = filterByCastType(ptY.rgn)
            // do pt(x) \cap (ptY f filtered by T)          
            val rgnInter = xRgn.intersect(filteredYRgn)
            if (rgnInter.isEmpty) {                    
              if (Options.PRINT_REFS) println("Refuted by definitely-failing cast")
              false // refuted by failed cast
            } else {
              val interVar = ObjVar(rgnInter)
              if (!qry.substitute(interVar, ptX, hg)) false                     
              else {
                if (!yEdge.isDefined) qry.addLocalConstraint(PtEdge.make(y, interVar))
                qry.substitute(interVar, ptY, hg)
              }
            }
          }
          
          def handleMissingYEdge() : Boolean = getPt(y, hg) match {
            case rgn if rgn.isEmpty => // x = (T) null
              val pNull = Qry.getNullVar(qry)
              qry.addLocalConstraint(PtEdge.make(y, pNull))
              true
            case rgn => handleObjY(ObjVar(rgn), None)
          }
          
          getConstraintEdge(y, qry.localConstraints) match {
            case yEdge@Some(LocalPtEdge(_, ptY@ObjVar(_))) => handleObjY(ptY, yEdge)
            case Some(LocalPtEdge(_, pureY@PureVar(_))) =>
              if (qry.isNull(pureY)) true
              else handleMissingYEdge
            case None => handleMissingYEdge
          }     
          
        case Some(e@LocalPtEdge(_, p@PureVar(_))) => // found edge x -> p; implicitly, p == null
          assert(p.isReferenceType)
          assert(!n.getIR().getSymbolTable().isConstant(s.getVal()))
          qry.removeLocalConstraint(e)
          if (qry.isNull(p)) {
            // since x is null, y must also be null
            val y = Var.makeLPK(s.getVal(), n, hm)
            getConstraintEdge(y, qry.localConstraints) match {
              case Some(LocalPtEdge(_, ObjVar(_))) => // we have y -> A, where A is non-null
                false
              case Some(LocalPtEdge(_, PureVar(_))) => // we have y -> null 
                true
              case None => // no y -> ... edge in our constraints. add y -> p (implicitly, p == null) constraint
                assert(p.isReferenceType)
                qry.addLocalConstraint(PtEdge.make(y, p))
                true
            }
          } else sys.error("non-null constraint")
        case None => // no edge x -> _
          val y = Var.makeLPK(s.getVal, n, hm)

          def filterByRegionAndAddEdge(yRgn : Set[InstanceKey]) : Boolean = {
            val filteredYRgn = filterByCastType(yRgn)
            if (filteredYRgn.isEmpty) false // refuted by definitely failing cast
            else {
              qry.addLocalConstraint(PtEdge.make(y, ObjVar(filteredYRgn)))
              true
            }
          }

          getConstraintEdge(y, qry.localConstraints) match {
            case Some(e@LocalPtEdge(_, ObjVar(yRgn))) => // found edge y -> _; filter
              qry.removeLocalConstraint(e)
              filterByRegionAndAddEdge(yRgn)
            case Some(_) => true // TODO: add new y edge here?
            case None =>
              val yRgn = PtUtil.getPt(y, hg)
              // TODO: do this for local constraints too?
              // we will choose to add a constraint on this cast succeeding if the target may-alias something else in our
              // constraints that has an incompatible type with the cast type T
              if (qry.heapConstraints.exists(e => e match {
                // yRgn and rgn overlap. filter yRgn by type and add x -> ObjVar(yRgn) constraint
                case ObjPtEdge(_, _, o@ObjVar(rgn)) if !rgn.intersect(yRgn).isEmpty && filterByCastType(rgn).isEmpty => true
                case _ => false
              })) filterByRegionAndAddEdge(yRgn)
              else true
          }
      }

    case s : SSAPiInstruction => // x = pi y for BLK, cause INSTR
      // this instruction means assign x to y filtered by the predicate in INSTR or its negation, depending on whether
      // BLK is the true branch target or false branch target
      getConstraintEdgeForDef(s, qry.localConstraints, n) match {
        case Some(e@LocalPtEdge(_, snk)) =>
          qry.removeLocalConstraint(e)
          // TODO: filter pt(y) by T or !T here instead of waiting. would get a refutation a bit faster by doing so
          /*s.getCause match {
            case i : SSAInstanceofInstruction => // y instanceof T
            case i => sys.error(s"Unimplemented cause instr $i")
          }*/
          qry.addLocalConstraint(PtEdge.make(Var.makeLPK(s.getVal, n, hm), snk))
          true
        case None => true
      }
      
    case s : SSAUnaryOpInstruction => // x = op y where op is !
      getConstraintEdgeForDef(s, qry.localConstraints, n) match {
        case Some(edge) =>
          if (Pure.isNegateOp(s.getOpcode())) {
            val rhs = getPureExprForLocal(s.getUse(0), qry, n, hm)
            qry.addPureConstraint(Pure.makeNeConstraint(edge.snk.asInstanceOf[PureExpr], rhs))
          } else{
            println(s"Unexpected negation operator ${s.getOpcode()} in instruction $s ir ${n.getIR()}; dropping constraints")
            qry.removeLocalConstraint(edge)
            true
          }
        case None => true
      }
      
    case s : SSABinaryOpInstruction => // x = y op z where op is +, -, *, /, %, etc.
      getConstraintEdgeForDef(s, qry.localConstraints, n) match {
        case Some(edge) => // found edge x -> v0
          // get or create v's such that y -> v1, z -> v2
          val (lhs, rhs) = (getPureExprForLocal(s.getUse(0), qry, n, hm), getPureExprForLocal(s.getUse(1), qry, n, hm))
          // add constraint v0 == v1 op v2 
          //qry.addPureConstraint(Pure.makeEqConstraint(edge.snk.asInstanceOf[PureExpr], PureBinExpr(lhs, s.getOperator(), rhs)))
          qry.addPureConstraint(Pure.makeEqConstraint(edge.snk.asInstanceOf[PureExpr], Pure.makePureBinExpr(lhs, s.getOperator(), rhs)))
        case None => true
      }      
      
    case s : SSALoadMetadataInstruction => // x = load_metadata token, type 
      getConstraintEdgeForDef(s, qry.localConstraints, n) match {
        case Some(edge) => // got edge x -> v
          s.getType() match {
            case t : TypeReference if t == TypeReference.JavaLangClass =>
              s.getToken() match {  
                case t : TypeReference => // x = y.class
                  val clazz = cha.lookupClass(t)
                  edge.snk match {
                    case ObjVar(rgn) => 
                       val ok = rgn.contains(new ConcreteTypeKey(clazz)) // check y.class == v
                       if (!ok && Options.PRINT_REFS) println("Refuted by loadMetadata instruction! ")                         
                       else qry.removeLocalConstraint(edge)                              
                       ok
                    case PureVar(_) => sys.error("Excpected ObjVar snk, but got PureVar snk in " + edge)
                  }                 
                case _ => Util.unimp("Load metadata instruction " + s)
              }
            case _ => Util.unimp("Load metadata instruction " + s)
          }
        case None => true 
      }
    
    // converting one kind of primitive type into another kind of primitive type
    case s : SSAConversionInstruction => // x = conversion(T) y where T is type of conversion
      handleUnsupportedInstruction(s, qry, n)
    
    // comparing floats, longs, and doubles
    case s : SSAComparisonInstruction =>
      handleUnsupportedInstruction(s, qry, n)
      
    case s : SSAGetCaughtExceptionInstruction => 
      handleUnsupportedInstruction(s, qry, n)      
    
    // locking primitives
    case s : SSAMonitorInstruction => // monitorenter or monitorexit
      true
     
    case s : SSAThrowInstruction => false // refuted by thrown exception
    case s : SSAGotoInstruction => true 
    case s => sys.error("unsupported instruction " + s)
  }
  
  private def handleUnsupportedInstruction(s : SSAInstruction, qry : Qry, n : CGNode) = 
    getConstraintEdgeForDef(s, qry.localConstraints, n) match {
      case Some(e) => 
        if (DEBUG) println("Unsupported instruction " + s + "; dropping constraints")
        qry.removeLocalConstraint(e)
        true
      case None => true // no matching edge
    }
  
  private def mayEq(vUse: Int, v : Val, localConstraints : MSet[LocalPtEdge], n : CGNode) : Boolean = {
    val tbl = n.getIR().getSymbolTable()
    val useConst = tbl.isConstant(vUse)
    v match {
      case ObjVar(rgn) =>                 
        if (useConst && !tbl.isStringConstant(vUse)) false // v is an objVar and thus cannot be null or another pure constant 
        else getPt(Var.makeLPK(vUse, n, hm), localConstraints, hg) match {
          case Some((ptV, _)) => !ptV.rgn.intersect(rgn).isEmpty
          case None => false // empty region means vUse is null, so it can't equal v 
        }
      case p@PureVar(_) =>
        if (useConst) {
          // TODO: add p == Pure.makePureVal(useConst) to constraints and ask Z3 if it's ok
          true
        } else {
          getConstraintEdge(Var.makeLPK(vUse, n, hm), localConstraints) match {
            case Some(edge) => edge.snk match {
              case snk@PureVar(_) =>         
                // TODO: add p == snk to constraints and ask Z3 if it's ok
                true
              case _ => sys.error("odd snk " + edge.snk)
            }
            case None => true // no idea what value y may hold, must assume a match  
          }
        }
    }
  }
  
  private def dropRelatedPureConstraints(v : Val, q : Qry) : Unit = v match {
    case p@PureVar(_) => // drop any pure constraints associated with p 
      q.pureConstraints.foreach(c => if (c.getVars().contains(p)) q.removePureConstraint(c))
    case _ => ()
  }
  
  private def dropPtEdge[T <: PtEdge](e : T, q : Qry, dropF : T => Unit, loopDrop : Boolean = false) : Unit = e.snk match {
    case ObjVar(_) => 
      if (!loopDrop) {
        if (DEBUG) println("dropping constraint " + e)
        dropF(e)
      }
    case p@PureVar(_) =>
      if (DEBUG) println("dropping constraint " + e)
      dropF(e)
      dropRelatedPureConstraints(p, q)
  }
  
  private def dropLocalConstraint(l : LocalPtEdge, q : Qry, loopDrop : Boolean) : Unit = 
    dropPtEdge(l, q, (e : LocalPtEdge) => q.removeLocalConstraint(e), loopDrop)
  
  private def dropHeapConstraint(h : HeapPtEdge, q : Qry, loopDrop : Boolean) : Unit =
    h.snk match {
    case ObjVar(_) => 
      if (!loopDrop) {
        if (DEBUG) println("dropping heap constraint " + h)
        q.removeHeapConstraint(h)
      }
    case PureVar(_) =>
      if (DEBUG) println("dropping heap constraint " + h)
      q.removeHeapConstraint(h)
      dropRelatedPureConstraints(h.snk, q)        
  }
  
  // if dropConstraints is true, drops constraints produceable by callee -- otherwise, returns true if callee is relevant to qry
  private def dropCallConstraintsOrCheckCallRelevant(callee : CGNode, heapConstraints : MSet[HeapPtEdge],
                                                     dropConstraints : Boolean, loopDrop : Boolean, qry : Qry) : Boolean = {
    val modKeys = modRef.get(callee).toSet // set of pointer keys modified by the callee function
    val staticFlds = // static fields declared by the callee function (if any)
      if (callee.getMethod().isClinit()) callee.getMethod().getDeclaringClass().getDeclaredStaticFields().toSet else Set.empty[IField]
    val reachableInits = { // constructors reachable from the callee function       
      val reachable = DFS.getReachableNodes(cg, java.util.Collections.singleton(callee))
      assert(reachable.contains(callee))
      reachable.foldLeft (Set.empty[IClass]) ((s, callee) => if (!callee.getMethod.isInit()) s
        else s + callee.getMethod().getDeclaringClass()) 
    }

    // drop constraints and keep going if we're in drop mode, just return true otherwise
    def maybeDrop(e : HeapPtEdge) = {
      if (dropConstraints) dropHeapConstraint(e, qry, loopDrop)
      if (DEBUG && !dropConstraints) println(s"Relevant: $e")
      !dropConstraints
    }
    
    qry.heapConstraints.exists(e => { e match {
      case e@ObjPtEdge(_, f : InterfaceMethodField, _) => false // special hack for synthesis; never drop
      case e@ObjPtEdge(ObjVar(rgn), InstanceFld(fld), PureVar(_)) if (Fld.isArrayLengthFld(fld))=>
        rgn.exists(k => modKeys.contains(hm.getPointerKeyForArrayLength(k))) // relevant because of array length
      case e@ObjPtEdge(ObjVar(rgn), InstanceFld(fld), _) => 
        (rgn.exists(k => modKeys.contains(hm.getPointerKeyForInstanceField(k, fld))) ||
        reachableInits.contains(fld.getDeclaringClass())) // relevant because of initialization to default values
      case e@StaticPtEdge(_, StaticFld(key), _) => modKeys.contains(key) || 
        staticFlds.contains(key.getField()) // relevant because of initialization to default values
      case e@ArrayPtEdge(arrRef, ArrayFld(keys, _, _), _) => !modKeys.intersect(keys.asInstanceOf[Set[PointerKey]]).isEmpty
    }} && maybeDrop(e))
  }

  // handle Java methods with special semantics like clone() and Class.isInstance()
  def handleJavaMagicMethod(i : SSAInvokeInstruction, caller : CGNode,
                            paths : List[Path]) : Option[(List[Path],List[Path])] =
    i.getCallSite.getDeclaredTarget match {
      case m if m.getDeclaringClass().getName() == CloneInterpreter.CLONE.getDeclaringClass().getName() &&
        m.getSelector() == CloneInterpreter.CLONE.getSelector() => // Object.clone() special case
        // TODO: factor out handleCallToObjectClone into TransferFunctions
        Some(Nil, paths.filter(p => handleCallToObjectClone(i, p.qry, caller)))
      case m if m.getDeclaringClass.getName == TypeReference.JavaLangClass.getName &&
          m.getName.toString == "isInstance" => // Class.isInstance() special case
        paths.foreach(p => {
          val qry = p.qry
          getConstraintEdgeForDef(i, qry.localConstraints, caller) match {
            case Some(e@LocalPtEdge(_, p@PureVar(_))) => // found edge x -> ptX
              // x.IsInstance(y) means the same as y instanceof x
              qry.removeLocalConstraint(e)
              val y = Var.makeLPK(i.getUse(1), caller, hm)
              getConstraintEdge(y, qry.localConstraints) match {
                case Some(LocalPtEdge(yVar, ObjVar(rgnY))) =>
                  if (qry.isDefinitelyTrue(p)) {
                    val x = Var.makeLPK(i.getUse(0), caller, hm)
                    // drop existing constraint on x; for maximum precision, we should not need to do this, but we have to
                    // because of a hack (see below)
                    getConstraintEdge(x, qry.localConstraints) match {
                      case Some(e) =>
                        qry.removeLocalConstraint(e)
                      case None => ()
                    }
                    val typeKeys = rgnY.foldLeft (Set.empty[InstanceKey]) ((keys, instanceKey) =>
                      keys + new ConcreteTypeKey(instanceKey.getConcreteType))
                    // add x -> {ConcreteTypeKey(z) for z in types(pt(y))} constraint. technically, this is a type error
                    // since the type of x is java.lang.Class however, this is just a hack to create a constraint that
                    // says typeof(x) \in typesof(pt(y)) without creating new constraint forms. the SSALoadMetadata
                    // instruction is the one to encounter this constraint, and it understands what to do with it
                    qry.addLocalConstraint(PtEdge.make(x, ObjVar(typeKeys)))
                  }/* else if (qry.isDefinitelyFalse(p)) {
                    // trickier case than the true case. this can be any type except for the type of something in pt(y)
                    // TODO: implement this case
                    ()
                  }*/ else ()
                case _ =>
                  // TODO: for maximum precision, could still add constraint in this case, but will be trickier
                  ()
              }
            case _ => ()
        }})
        Some(Nil, paths)
      case m => None
    }

  def isRetvalRelevant(i : SSAInvokeInstruction, caller : CGNode, qry : Qry) =
    i.hasDef() && {
      val lhs = LocalVar(Var.makeLPK(i.getDef(), caller, hm))
      qry.localConstraints.exists(e => e.src == lhs)
    }

  def isCallRelevant(i : SSAInvokeInstruction, caller : CGNode, callee : CGNode, qry : Qry) : Boolean =
    isRetvalRelevant(i, caller, qry) ||
    dropCallConstraintsOrCheckCallRelevant(callee, qry.heapConstraints, dropConstraints = false, loopDrop = false, qry)
  
  private def dropCallConstraints(qry : Qry, callee : CGNode, 
    modRef : java.util.Map[CGNode,com.ibm.wala.util.intset.OrdinalSet[PointerKey]], loopDrop : Boolean) : Unit = 
    dropCallConstraintsOrCheckCallRelevant(callee, qry.heapConstraints, dropConstraints = true, loopDrop, qry)
  
  def dropConstraintsFromInstructions(i : Iterable[SSAInstruction], n : CGNode, qry : Qry, callee : Option[CGNode] = None, loopDrop : Boolean = false) : Unit = {
    require(Util.implies(callee.isDefined, i.forall(i => i.isInstanceOf[SSAInvokeInstruction])))
    // important to do this first; otherwise we may unsoundly assume a local binding holds when it can in fact be reassigned in a loop
    // qry.node check is because we only need to drop local constraints for the current node (not for callees, 
    // because we won't have any)
    if (qry.node == n) i.foreach(i => dropLocalConstraintsFromInstruction(i, qry, loopDrop))

    i.foreach(i => dropHeapConstraintsFromInstruction(i, n, qry, modRef, loopDrop, callee))
  }
        
  def dropLocalConstraintsFromInstruction(i : SSAInstruction, qry : Qry, loopDrop : Boolean = false) = 
    if (i.hasDef) { // drop local constraints with i's def as LHS
      val lhs = LocalVar(Var.makeLPK(i.getDef(), qry.node, hm))
      qry.localConstraints.find(e => e.src == lhs) match {
        case Some(e) => dropLocalConstraint(e, qry, loopDrop)
        case None => ()
      }
    }
    
  def dropHeapConstraintsFromInstruction(i : SSAInstruction, n : CGNode, qry : Qry, 
                                         modRef : java.util.Map[CGNode,com.ibm.wala.util.intset.OrdinalSet[PointerKey]],
                                         loopDrop : Boolean, callee : Option[CGNode] = None) : Unit = {

    val (localConstraints, heapConstraints) = (qry.localConstraints, qry.heapConstraints)

    i match { // drop heap constraints that may be modified by the instruction
      case i : SSAPutInstruction => // x.f = y
        val fld = Fld.make(i.getDeclaredField(), hm, cha)
        heapConstraints.foreach(e => if (e.fld == fld) { // check that f and e.fld are the same fld
          // check that y and e.snk can refer to the same value
          if (mayEq(i.getVal(), e.snk, localConstraints, n) && { e.src match {
            // check that x and e.src can refer to the same value
            case eSrc@ObjVar(rgn) =>
              val x = Var.makeLPK(i.getRef(), n, hm)
              getPt(x, localConstraints, hg) match {
                case Some((ptX, _)) => !ptX.rgn.intersect(rgn).isEmpty
                case None => sys.error("Empty region fcor " + x)
              }                     
            case ClassVar(c) => true
          }}) dropHeapConstraint(e, qry, loopDrop) // src and snk both match -- need to drop this constraint
        })
      case i : SSAArrayStoreInstruction => // x[i] = y
        heapConstraints.foreach(e => e match {
          case ArrayPtEdge(arr, _, snk) => // no need to check fld equality since it is the same as x equality for arrays 
            if (mayEq(i.getArrayRef(), arr, localConstraints, n) // check that x and e.src can refer to the same value
                && mayEq(i.getValue(), snk, localConstraints, n)) { // check that y and e.snk can refer to the same value
                  dropHeapConstraint(e, qry, loopDrop)
            }
            case _ => ()
          })  
      case i : SSANewInstruction if i.getNewSite().getDeclaredType().isArrayType() => // x = new T() where T is an array type
        // this instruction implicitly assigns to the array's length field and initializes the contents of the array to default values
        // drop all remaining constraint ons        
        val allocatedKey = hm.getInstanceKeyForAllocation(n, i.getNewSite())
        heapConstraints.foreach(e => e.src match {          
          //case ObjVar(rgn) if rgn.contains(allocatedKey) => 
          case ObjVar(rgn) => 
            if (rgn.contains(allocatedKey)) {
              if (Fld.isArrayLengthFld(e.fld)) dropHeapConstraint(e, qry, loopDrop) // drop constraint on array length
              else e.snk match {
                case p@PureVar(_) =>
                  try {
                    if (qry.checkTmpPureConstraint(Pure.makeDefaultValConstraint(p)))
                      // drop constraint; might be consumed by initialization to default values
                      dropHeapConstraint(e, qry, loopDrop)
                  } catch {
                    case _ : UnknownSMTResult => dropHeapConstraint(e, qry, loopDrop)
                  }
                case _ => ()
              }
            }
          case _ => ()
        })
        
      case i : SSAInvokeInstruction =>

        def dropEdgeIfConsumedByInitToDefaultVals(e : HeapPtEdge) = e.snk match {
          case p@PureVar(_) =>
            try {
              if (qry.checkTmpPureConstraint(Pure.makeDefaultValConstraint(p))) {
                assert(!e.snk.isArrayType) // TODO: initialize array contents to default vals?
                dropHeapConstraint(e, qry, loopDrop)
              } // else, initialization to pure vars would not produce e
            } catch {
              case _ : UnknownSMTResult => dropHeapConstraint(e, qry, loopDrop)
            }
          case ObjVar(_) => () // no need to drop; initialization to default values can't assign an objet (only null)
        }   

        cha.resolveMethod(i.getDeclaredTarget()) match {
          case null => ()
          case m => if (m.isInit()) { // drop constraints that can be produced by default value initialization
            val initClass = m.getDeclaringClass()          
            val relevantEdges = heapConstraints.collect({ case e@ObjPtEdge(_, fld, p@PureVar(_)) if fld.fld.getDeclaringClass() == initClass => e } )
            if (!relevantEdges.isEmpty) {
              val receiver = Var.makeLPK(i.getUse(0), n, hm)
              getConstraintEdge(receiver, localConstraints) match {
                case Some(e0) => relevantEdges.foreach(e1 => if (e0.src == e1.src) dropEdgeIfConsumedByInitToDefaultVals(e1))
                case None => 
                  val ptReceiverRgn = getPt(receiver, hg)
                  if (!ptReceiverRgn.isEmpty) 
                    relevantEdges.foreach(e => if (!e.src.rgn.intersect(ptReceiverRgn).isEmpty) dropEdgeIfConsumedByInitToDefaultVals(e))
              }              
            }
          } else if (m.isClinit()) {
            val clinitClass = m.getDeclaringClass()
            val relevantEdges = heapConstraints.collect({ case e@StaticPtEdge(ClassVar(cls), f, p@PureVar(_)) if cls == clinitClass => e})
            relevantEdges.foreach(e => dropEdgeIfConsumedByInitToDefaultVals(e))
          }        
        }
        
        // create list of types that the receiver of this method may be
        val okClasses = if (!i.isStatic()) {
          val receiver = Var.makeLPK(i.getUse(0), n, hm)
          getConstraintEdge(receiver, localConstraints) match {
            case Some(LocalPtEdge(_, ObjVar(rgn))) =>                            
              rgn.foldLeft (Set.empty[IClass]) ((s, key) => s + key.getConcreteType())
            case Some(LocalPtEdge(_, p@PureVar(_))) =>
              assert(p.isReferenceType, "PureVar " + p + " is non-reference type")
              Set.empty[IClass] // null dispatch, don't have to drop anything
            case None => Set.empty[IClass]
          }
        } else Set.empty[IClass]
        
        val targets = callee match {
          case Some(callee) => Iterable(callee)
          case None => cg.getPossibleTargets(n, i.getCallSite()).toIterable
        }
        // drop constraints from all instructions in each feasible method call according to okClasses
        targets.foreach(n => {
          if (n.getIR() != null && (okClasses.isEmpty || okClasses.contains(n.getMethod().getDeclaringClass()))) {
            // drop constraints from all instructions in n
            dropCallConstraints(qry, n, modRef, loopDrop)
            // TODO: the commented-out code blows up the call stack. we could rewrite this method to be tail-rec, but is it worth it?
            //dropConstraintsFromInstructions(n.getIR().iterateAllInstructions().toIterable, n, qry, cg, modRef)
          }
        })
          
      case _ => () // other instructions can't modify the heap
    }

  }
  
  def dropLoopWriteableConstraints(qry : Qry, loopHead : ISSABasicBlock, n : CGNode) : Unit = {
    if (DEBUG) println("Doing loop drop for " + qry.id + " head " + loopHead)
    val loopInstrs = edu.colorado.thresher.core.WALACFGUtil.getInstructionsInLoop(loopHead.asInstanceOf[SSACFG#BasicBlock], n.getIR()).toSet
    dropConstraintsFromInstructions(loopInstrs, n, qry, callee = None,
      // do *not* flip loopDrop to true -- it causes problems
      loopDrop = false)


  }
              
}
