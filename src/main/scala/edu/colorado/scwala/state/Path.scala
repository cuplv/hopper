package edu.colorado.scwala.state

import scala.collection.JavaConversions._
import com.ibm.wala.analysis.pointers.HeapGraph
import com.ibm.wala.ipa.callgraph.CGNode
import com.ibm.wala.ipa.callgraph.CallGraph
import com.ibm.wala.ipa.callgraph.propagation.HeapModel
import com.ibm.wala.ipa.cha.IClassHierarchy
import com.ibm.wala.ssa.ISSABasicBlock
import com.ibm.wala.ssa.SSAArrayStoreInstruction
import com.ibm.wala.ssa.SSAConditionalBranchInstruction
import com.ibm.wala.ssa.SSAInstruction
import com.ibm.wala.ssa.SSAInvokeInstruction
import com.ibm.wala.ssa.SSAPhiInstruction
import com.ibm.wala.ssa.SSAPutInstruction
import edu.colorado.scwala.executor.TransferFunctions
import edu.colorado.scwala.translate.WalaBlock.fromISSABasicBlock
import edu.colorado.scwala.translate.WalaBlock.fromWalaBlock
import edu.colorado.scwala.util.CFGUtil
import edu.colorado.scwala.util.CGNodeUtil
import edu.colorado.scwala.util.ClassUtil
import edu.colorado.scwala.util.PtUtil
import edu.colorado.scwala.util.Util
import Path._
import edu.colorado.thresher.core.Options
import com.ibm.wala.classLoader.{IClass, IMethod}
import com.ibm.wala.types.MethodReference
import com.ibm.wala.types.TypeReference
import com.ibm.wala.types.ClassLoaderReference
import edu.colorado.scwala.translate.Concretizable
import edu.colorado.scwala.translate.MinSet
import edu.colorado.scwala.translate.WalaBlock

object Path {
  val MAX_CALLSTACK_DEPTH = Options.MAX_CALLSTACK_DEPTH + 1
  
  val methodNameBlacklist = Set("toString", "equals", "hash", "println", "print", "indexOf", "append", "charAt", "hashCode", "intValue", "parseInt", "eq")
  val classNameBlacklist = Set("Ljava/io/PrintWriter", "Ljava/lang/String", "Ljava/security/AccessController", "Ljava/lang/Character", "Lsun/misc/VM",
                               "Ljava/lang/Class", "Ljava/io/BufferedReader", "Ljava/lang/Float")  
  
  val SYSTEM_EXIT = MethodReference.findOrCreate(TypeReference.findOrCreate(ClassLoaderReference.Primordial, "Ljava/lang/System"), "exit", "(I)V")
  
  def methodBlacklistContains(method : IMethod) : Boolean = {
    //ClassUtil.isLibrary(method) || // TODO: TMP!
    methodNameBlacklist.contains(method.getName().toString()) ||
    classNameBlacklist.contains(method.getDeclaringClass().getName().toString())
  }
  
  var idCounter : Int = 0
  def newId : Int = {
    idCounter += 1    
    idCounter 
  }
  
  def ppPaths(paths : List[Path]) : Unit = { paths.foreach(p => print(p.id + " ")); println }
  
  private val DEBUG = false  
  
   // TODO: this shouldn't live here. find someplace reasonable to putit
  /**
   * @return list of paths representing the result of pushing @param p to each instruction in @param instrs
   */
  def fork(p : Path, node : CGNode, instrs : Set[SSAInstruction], jmpNum : Int, cg : CallGraph, hg : HeapGraph, hm : HeapModel, cha : IClassHierarchy, 
           paths : List[Path] = Nil) : List[Path] = {   
    val alreadyDidInitCase = Util.makeSet[CGNode]
    //val fakeWorldClinit = WALACFGUtil.getFakeWorldClinitNode(cg) 
    val fakeWorldClinit = CGNodeUtil.getFakeWorldClinitNode(cg).get
    
    instrs.foldLeft (paths) ((paths, instr) => {
      val newPath = p.deepCopy
      CFGUtil.findInstr(node, instr) match {
        case Some((blk, index)) => 
          setupJumpPath(newPath, instr, blk, index, node, hm, hg, cha, jmpNum)    
          newPath :: paths
        case None => 
          // this happens when we get an instruction that is one of our custom-generated
          // "initialize instance/static fields to default value" instructions
          // we handle this by just writing default values to all fields in the current query and
          // then setting the current location to "just finished executing the init / class init"
          // so, this is a terrible hack. can get rid of it once we have our own IR/CFG representation
          assert(!instr.isInstanceOf[SSAArrayStoreInstruction])
          val method = node.getMethod()
          if (method.isInit()) {
            // make sure we only execute the init case for each node once. this is because there may be multiple
            // initialization to default value instructions for a given node, but we don't want to do a separate
            // case split for each one. instead, we consider a single case where we initialize every field to its
            // default value in one go.
            if (alreadyDidInitCase.add(node)) {
              setupJumpPath(newPath, instr, node.getIR().getControlFlowGraph().entry(), -1, node, hm, hg, cha, jmpNum)
              newPath.qry.localConstraints.find(e => e match {
                case LocalPtEdge(LocalVar(key), ObjVar(_)) => key.getValueNumber() == 1                  
                case _ => false
              }) match {
                case Some(LocalPtEdge(_, receiverObj@ObjVar(_))) =>
                  if (TransferFunctions.initializeInstanceFieldsToDefaultValues(newPath.qry, node, Set(receiverObj))) newPath :: paths
                  else paths // refuted by initialization to default vals
                case other => sys.error("Couldn't find local pointer to receiver in " + newPath + "; got " + other)
              }            
            } else paths // refuted by initialization to default values or we already did the init case for this node
          } else if (method.isClinit() || node.equals(fakeWorldClinit)) {
            if (TransferFunctions.initializeStaticFieldsToDefaultValues(newPath.qry, fakeWorldClinit)) {
              setupJumpPath(newPath, instr, fakeWorldClinit.getIR().getControlFlowGraph().entry(), -1, node, hm, hg, cha, jmpNum)
              newPath :: paths
            } else paths // refuted by initialization to default values
          } else sys.error("Couldn't find instr " + instr + " in " + node + " ir " + node.getIR())           
      }
    })  
  }
  
  def setupJumpPath(p : Path, instr : SSAInstruction, node : CGNode, hm : HeapModel, hg : HeapGraph, cha : IClassHierarchy, jmpNum : Int = 0) : Unit = {
    val (blk, index) = CFGUtil.findInstr(node, instr) match {
      case Some(p) => p
      case None => sys.error("Couldn't find instr " + instr + " in node " + node)
    }
    setupJumpPath(p, instr, blk, index, node, hm, hg, cha, jmpNum)
  }
  
  def setupJumpPath(p : Path, i : SSAInstruction, blk : ISSABasicBlock, index : Int, node : CGNode, hm : HeapModel, hg : HeapGraph, cha : IClassHierarchy, jmpNum : Int) = {
    val qry = p.qry
    require(qry.callStack.isEmpty)      
   
    val jmpLoc = new CallStackFrame(node, Util.makeSet[LocalPtEdge], blk, index)
    qry.callStack.push(jmpLoc)
    // need distinct copies because the StackFrame on the call stack will be mutated
    val copy = jmpLoc.clone
    assert(!p.jumpMap.values.toSet.contains(copy), "already jumped to " + jmpLoc)
    p.jumpMap += (jmpNum -> copy)
    p.jumpHistory += copy
            
    // we need to set up x to point to the base obj A of the constraint A.f -> B or A[i] -> B to be consumed
    def addLocalConstraintOnLHS(lhs : ObjVar, lhsLocNum : Int) = {
      val x = Var.makeLPK(lhsLocNum, node, hm)
      val ptX = PtUtil.getPt(x, hg)            
      val rgnInter = ptX.intersect(lhs.rgn)
      assert(!rgnInter.isEmpty)
      val interVar = ObjVar(rgnInter)
      val res = qry.substitute(interVar, lhs, hg)
      assert(res)
      qry.addLocalConstraint(PtEdge.make(x, interVar))
    }
    
    // TODO: add context-sensitivity constraints from node
    // setup local constraints based on instruction we're jumping to
    // the idea is that we're jumping to an instruction that will consume some edge in our constraints,
    // so we set up the local constraints in a way that guarantee the edge will be consumed
    i match {
      case i : SSAPutInstruction => // x.f = y
        if (!i.isStatic()) { // if it's static, no setup necessary
          val consumed = qry.heapConstraints.collect({ case e@ObjPtEdge(_, InstanceFld(fld), _) if cha.resolveField(i.getDeclaredField) == fld => e})
          assert(consumed.size == 1, "Got consumed set " + consumed) // only expecting one edge to be consumed by a given instruction
          addLocalConstraintOnLHS(consumed.head.src, i.getRef())        
        }
      case i : SSAArrayStoreInstruction => // x[i] = y
        val consumed = qry.heapConstraints.collect({ case e@ArrayPtEdge(_, _, _) => e })
        assert(consumed.size == 1, "Got consumed set " + consumed) // only expecting one edge to be consumed by a given instruction
        addLocalConstraintOnLHS(consumed.head.src, i.getArrayRef())        
      case s => sys.error("Implement me: setup for " + s)
    }
  }
  
}

class Path(val qry : Qry, var lastBlk : WalaBlock = null,
           private var exceptionTypes : Iterable[IClass] = Nil) extends Concretizable {
  val id : Int = newId
  // map from jump number to jump location
  private val jumpMap = Util.makeMap[Int,CallStackFrame] // piecewise only
  private val jumpHistory = Util.makeSet[CallStackFrame]
  // TODO: this is kind of a hack, but not sure how else to do it with piecewise (can't live in the symbolic executor...)
  // switch blocks for which we have already added the switch constraints
  val switchConstraintsAdded = Util.makeSet[ISSABasicBlock]
  // if the path is currently exceptional, we need to know what kind of exception could have been thrown to get the path
  // to where it is previosuly. it is the symbolic executor's path to tell each path when it becomes exceptional and
  // what exception type(s) led to it being exceptional

  def callStack = qry.callStack
  def node : CGNode = callStack.top.node
  def blk : WalaBlock = callStack.top.blk
  def index : Int = callStack.top.index  
  
  def deepCopy(q : Qry) : Path = {    
    val path = new Path(q, lastBlk, exceptionTypes)
    // copy call stack
    // copy jump map
    this.jumpMap.foreach(kvPair => path.jumpMap += kvPair)
    assert(this.jumpMap.size == path.jumpMap.size)
    this.switchConstraintsAdded.foreach(blk => path.switchConstraintsAdded += blk)    

    if (DEBUG) {
      assert(path.qry.id != this.qry.id, "unecessary copy of query " + qry.id)
      println("made path " + path.id + "X from path " + this.id + "X")
      println("made qry " + path.qry.id + " from " + this.qry.id + " lineage " + path.qry.parents)
      assert(qry.checkPureConstraintsSAT, "shouldn't make copies of infeasible paths! " + qry + " lineage " + qry.parents)
    }
    path
  }
    
  def deepCopy : Path = deepCopy(qry.clone)
    
  /** "normal" return from callee to caller */
  def returnFromCall(i : SSAInvokeInstruction, callee : CGNode, tf : TransferFunctions) : Boolean = {
    // TODO: for testing qry!
    val res0 = tf.returnToCallerNormal(qry)        
    
    res0
  }
  
  /** return from callee to an arbitrary caller (i.e., we have no context) */
  def returnFromCall(caller : CGNode, callee : CGNode, callBlk : WalaBlock, callLine : Int, invoke : SSAInvokeInstruction, tf : TransferFunctions) : Boolean = {    
    val res0 = tf.returnToCallerContextFree(invoke, qry, caller, callBlk, callLine)
    if (DEBUG) println("Done with return from " + ClassUtil.pretty(callee) + " to " + caller + " result is " + res0)
    res0    
  }
  
  def executeInstr(i : SSAInstruction, tf : TransferFunctions) : Option[List[Path]] = {    
    // TODO: for testing qry!
    tf.execute(i, qry, node) match {
      case l if l.isEmpty => None
      case l if l.size == 1 =>
        if (l.head.qry.id == this.qry.id) Some(List(this))
        else Some(List(this.deepCopy(l.head)))
      case l => Some(l.map(q => if (q eq this.qry) this else this.deepCopy(q)))
    }    
  }
  
  def dropReturnValueConstraints(invoke : SSAInvokeInstruction, caller : CGNode, tf : TransferFunctions) : Unit = 
    tf.dropLocalConstraintsFromInstruction(invoke, qry)
  
    
  def isCallRelevant(i : SSAInvokeInstruction, caller : CGNode, callee : CGNode, tf : TransferFunctions) : Boolean = {
    val res0 = tf.isCallRelevant(i, caller, callee, qry)
    //assert(res0 == res1, 
    //assert(Util.implies(res1, res0), "old says " + res1 + " new says " + res0) 
    res0
  }
    
  // TODO: redo this the right way when we're no longer using old queries
  def dropConstraintsProduceableInCall(invoke : SSAInvokeInstruction, caller : CGNode, callee : CGNode, tf : TransferFunctions) : Unit = {
    val cg = tf.cg
    tf.dropConstraintsFromInstructions(List(invoke), caller, qry, Some(callee))
    
    //this.qry.dropReturnValueConstraintsForCall(invoke, caller)
    // this check doesn't account for return values, so we drop them above 
    //if (this.qry.getRelevantNodes().values().flatten.toSet.contains(callee)) {
      //this.qry.dropConstraintsProduceableInCall(invoke, caller, callee, true)
    //}   
  }
  
  def executePhi(phi : SSAPhiInstruction, phiIndex : Int, tf : TransferFunctions) : Boolean = {
    val res0 = tf.executePhi(phi, phiIndex, qry, node)
    res0
  }
  
  def isDispatchFeasible(call : SSAInvokeInstruction, caller : CGNode, callee : CGNode, tf : TransferFunctions) : Boolean = 
    tf.isDispatchFeasible(call, caller, callee, qry)   
    
   // TODO: should we have a special flag for this instead?
  def isClinitPath(cg : CallGraph) : Boolean = {
    val fakeWorldClinit = CGNodeUtil.getFakeWorldClinitNode(cg).get //WALACFGUtil.getFakeWorldClinitNode(cg)
    qry.callStack.stack.exists(frame => frame.node.equals(fakeWorldClinit) || frame.node.getMethod().isClinit() || (
    //callStack.exists(frame => frame.node.equals(fakeWorldlClinit) || frame.node.getMethod().isClinit() || (
    cg.getPredNodeCount(frame.node) == 1 && cg.getPredNodes(frame.node).contains(fakeWorldClinit)))
  }
    
  //def popCallStack : StackFrame2 = qry.callStack.pop//this.callStack.pop
  def popCallStack : CallStackFrame = qry.callStack.pop//this.callStack.pop
  
  //def clearCallStack : Unit = this.callStack.clear
  def clearCallStack() : Unit = qry.callStack.clear     
  
  def callStackSize : Int = qry.callStack.size//this.callStack.size
  
  def callStackIter : Iterable[CallStackFrame] = this.callStack.stack
  
  //def printCallStack : Unit = this.callStack.foreach(f => print(f + " "))
  
  def isInJump : Boolean = !this.jumpMap.isEmpty
  
  def containsJump(jmpNum : Int) : Boolean = jumpMap.contains(jmpNum)
  
  def removeJump(jmpNum : Int) : Unit = {
    require(jumpMap.contains(jmpNum))
    if (DEBUG) println("On path " + id + "X, removing jump " + jmpNum)
    jumpMap -= jmpNum 
  }
  
  //def jumpHistoryContains(f : StackFrame2) : Boolean = this.jumpHistory.contains(f)
  def jumpHistoryContains(f : CallStackFrame) : Boolean = this.jumpHistory.contains(f)
  
  
  def foundWitness : Boolean = {    
    val res0 = qry.foundWitness//qry.foundWitness
    //if(res0 != res1) println("disagreement: old " + res1 + " new " + res0+ " old " + qry + " new " + qry)
    res0
  }

  def initializeStaticFieldsToDefaultValues : Boolean = {
    // TODO: for testing qry!
    val res0 = TransferFunctions.initializeStaticFieldsToDefaultValues(qry, this.node)
    //assert(res0 == res1, "new and old query disagree old " + res1 + " new " + res0 + " qry " + qry)
    res0
  }
  
  def setIndex(newIndex : Int) : Unit = callStack.top.index = newIndex
  
  def setNode(node : CGNode) : Unit = {
    val ir = node.getIR()
    if (ir != null) {
      val exitBlk = ir.getControlFlowGraph().exit()
      if (!this.callStack.isEmpty) assert(this.node != node, "adding dup " + node + " to stack")
      //callStack.push(new StackFrame2(node, exitBlk, exitBlk.size - 1)) // start at last instr
      qry.callStack.push(new CallStackFrame(node, Util.makeSet[LocalPtEdge], exitBlk, exitBlk.size - 1))
    }
  }

  def isExceptional : Boolean = !this.exceptionTypes.isEmpty

  // check if this path has a caught exception type T_caught such that there exists T_thrown \in @param thrownTypes and
  // T_thrown <: T_caught
  def couldCatchThrownExceptionType(thrownTypes : Iterable[IClass], cha : IClassHierarchy) =
    this.exceptionTypes.exists(caughtType =>
      thrownTypes.exists(thrownType => cha.isAssignableFrom(caughtType, thrownType)))

  def clearExceptionTypes() : Unit = this.exceptionTypes = Nil

  def setExceptionTypes(exceptionTypeRefs : Iterable[TypeReference], cha : IClassHierarchy) = {
    this.exceptionTypes = exceptionTypeRefs.map(typ => cha.lookupClass(typ))
  }

  def setBlk(newBlk : WalaBlock) : Unit = {
    lastBlk = callStack.top.blk
    callStack.top.blk = newBlk
    callStack.top.index = newBlk.size - 1
  }   
  
  def handleCallToObjectClone(i : SSAInvokeInstruction, tf : TransferFunctions) : Boolean = {
    // special case for object clone, which is a magic method in Java
    val res = tf.handleCallToObjectClone(i, qry, node)
    if (DEBUG && !res) println("Refuted by bad call to Object.clone!")
    res
  }

  def enterCallee(i : SSAInvokeInstruction, callee : CGNode, tf : TransferFunctions) : Boolean = {
    // TODO: for testing qry!
    tf.enterCallee(i, qry, node, callee)
    //qry.enterCall(i, callee, oldPath)
  }
  
  def addConstraintFromConditional(i : SSAConditionalBranchInstruction, isThenBranch : Boolean, tf : TransferFunctions) : Boolean = {
    val res0 = tf.executeCond(i, qry, node, isThenBranch)
    res0
  }
  
  def constrainBasedOnSwitchCases(cases : Iterable[SSAConditionalBranchInstruction], tf : TransferFunctions) : Boolean = {
    tf.constrainBasedOnSwitchCases(cases, qry, node)
  }
 
  def addConstraintFromSwitch(i : SSAConditionalBranchInstruction, tf : TransferFunctions, negated : Boolean = false) : Boolean = { 
    val res0 = tf.executeCond(i, qry, node, !negated)    
    res0
  }

  def dropLoopProduceableConstraints(loopHeader : ISSABasicBlock, tf : TransferFunctions) : Unit = 
    tf.dropLoopWriteableConstraints(qry, loopHeader, node)
    //qry.removeLoopProduceableConstraints(loopHeader.asInstanceOf[SSACFG#BasicBlock], node)
    
  def maybeWiden(inv : MinSet[Path]) : Boolean = {
    this.qry match {
      /*
      case qry : CombinedPathAndPointsToQuery =>
        val pathConstraints = qry.getConstraints().toSet
        val varConstraintMap = pathConstraints.groupBy(c => c.getVars())    
        // TODO: also want to widen if there is some constraint in this that has the same pathVars as a constraint
        // in some path in inv, but is not the same constraint AND is not a negated version of the same constraint
        // meant to handle the v1 >= v2 , v1 + 1 >= v2, v1 + 2 >= v2, ... constraints we see at loop heads        
        val pathVars = qry.pathVars
        
        // this.qry contains two constraints with same vars and one of them is not simple
        val toDrop = 
          varConstraintMap.foldLeft (new java.util.HashSet[PointerVariable]) ((set, pair) => {
            if (pair._2.size > 1 && pair._2.exists(c => !c.isSimple())) set.addAll(pair._1)
            set
          })
        
        val toDrop =
        inv.foldLeft (new java.util.HashSet[PointerVariable]) ((set, p) => p.qry match {
          case otherQry : CombinedPathAndPointsToQuery => otherQry.getConstraints().find(constraint =>
            !pathConstraints.contains(constraint) && varConstraintMap.contains(constraint.getVars())
            && pathConstraints.contains(constraint.negate()) && varConstraintMap(constraint.getVars()).size > 1)
            //&& (!constraint.isSimple() || !pathConstraints.contains(constraint.negate())))
            match { 
              case Some(constraint : Constraint) => set.addAll(constraint.getVars())
              case None => ()                
            }
            set
          case qry => sys.error("don't know what to do with query " + qry)
        })
        if (!toDrop.isEmpty()) {
          println("policy 2 widening " + qry)
          qry.dropConstraintsContaining(toDrop)
          sys.error("fixMe")
          //inv.foreach(p => p.qry.dropConstraintsContaining(toDrop))
          println("policy 2 widened to " + qry + "inv widened to " + inv)
          true
        } else false       
        */ 
      case qry => sys.error("don't know what to do with query " + qry)
    }
  }
  
  /*
  // TODO: push this into transfer functions once they are in Scala
  // TODO: clean up a bit, maybe limit to single policy?
  def maybeWiden(inv : MinSet[Path]) : Boolean = {
    this.qry match {
      case qry : CombinedPathAndPointsToQuery =>
        val pathConstraints = qry.getConstraints().toSet
        val varConstraintMap = pathConstraints.groupBy(c => c.getVars())
        // if this has more than one path constraint on a single PointerVariable, we suspect that this variable may be involved
        // in a loop condition. drop all constraints containing this variable in order to avoid divergence
        //qry.constraints().foldLeft(c => c.asInstanceOf[Constraint].getVars())
        val toDrop = varConstraintMap.foldLeft (new java.util.HashSet[PointerVariable]) ((set, pair) => {          
          if (pair._2.size > 1) set.addAll(pair._1)
          set
        })
        if (!toDrop.isEmpty()) {
          println("policy 1 widening " + qry)
          qry.dropConstraintsContaining(toDrop)
          println("policy 1 widened to " + qry)
          true
        } else {
          // TODO: also want to widen if there is some constraint in this that has the same pathVars as a constraint
          // int some path in inv, but is not the same constraint
          // meant to handle the v1 >= v2 , v1 + 1 >= v2, v1 + 2 >= v2, ... constraints we see at loop heads        
          val pathVars = qry.pathVars
          val toDrop =
            inv.foldLeft (new java.util.HashSet[PointerVariable]) ((set, p) => p.qry match {
              case otherQry : CombinedPathAndPointsToQuery => otherQry.getConstraints().find(constraint =>
                !pathConstraints.contains(constraint) && varConstraintMap.contains(constraint.getVars()))
                  match { 
                    case Some(constraint : Constraint) => set.addAll(constraint.getVars())
                    case None => ()                
                  }
                  set
              case qry => sys.error("don't know what to do with query " + qry)
            })
          if (!toDrop.isEmpty()) {
            println("policy 2 widening " + qry)
            qry.dropConstraintsContaining(toDrop)
            println("policy 2 widened to " + qry)
            true
          } else false
        }
    
      case qry => sys.error("don't know what to do with query " + qry)
    }
  }*/
  
  /**
   * @return true if this path entails other, false otherwise
   * @param this path entails the @param other path if the concretization of the other query is larger
   * than the concretization of this query
   * 
   * qry1.contains(qry2) returns true if qry1 has *all* of qry2's points-to edges
   * thus, qry1 |= qry2 if qry1.contains(qry2)
   */
  override def |=(other : Concretizable) : Boolean = other match {
    case p : Path =>
      (this.qry |= p.qry) && (!Options.SOUND_EXCEPTIONS || this.exceptionTypes == p.exceptionTypes)
      //assert(Util.implies(res1, res0), 
          //"disagreement on |=: old says " + res1 + " new says " + res0 + " OLD: " + qry + "\n|=\n" + other.qry + " and NEW " + qry + "\n|=\n" + p.qry)
      //assert(res0 == res1, "disagreement on |=: old says " + res1 + " new says " + res0 + " OLD: " + qry + "|=" + other.qry + " and NEW " + qry + "|=" + p.qry)
      //if (res0 != res1) println("disagreement on |=: old says " + res1 + " new says " + res0 + " OLD: " + qry + "|=" + other.qry + " and NEW " + qry + "|=" + p.qry)
  }
  
  /**
   * @return true if this path entails set, false otherwise
   * @param this path entails @param set if the concretization of the the set is larger than or equal to
   * the concretization of this query
   */
  override def |=(set : MinSet[Concretizable]) : Boolean = set.exists(p => this |= p)
  
  override def equals(other : Any) = other match { 
    case p : Path => this.qry.equals(p.qry) && (!Options.SOUND_EXCEPTIONS || this.exceptionTypes == p.exceptionTypes)
    case _ => false
  }
   
  override def hashCode =
    if (Options.SOUND_EXCEPTIONS && isExceptional) Util.makeHash(List(qry, exceptionTypes))
    else qry.hashCode //qry.hashCode
  override def toString = id + "X: " + qry.toString
}