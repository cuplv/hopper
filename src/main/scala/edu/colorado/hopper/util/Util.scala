package edu.colorado.hopper.util

import scala.collection.mutable.SetLike
import scala.collection.mutable.LinkedHashMap
import scala.collection.mutable.LinkedHashSet
import scala.collection.immutable.ListSet
import scala.compat.Platform
import scala.collection.mutable.MutableList
import com.ibm.wala.shrikeBT.IConditionalBranchInstruction.Operator._
import com.ibm.wala.shrikeBT.BinaryOpInstruction
import Types._
import java.io.File

object Util {
  
  /** no-op test function */
  def RET_TRUE(x : Any) : Boolean = true
  /** no-op thunk */
  def NOP(x : Any) : Unit = ()
  
  /** assertions and preconditions */
  def Assert(b : Boolean) : Unit = Assert(b, "")
  def Assert(b : Boolean, s : String) : Unit = if (!b) sys.error(s)
  def Require(b : Boolean) : Unit = Assert(b, "")
  
  /** data structures */
  def makeList[T] = new MutableList[T]
  // return mutable sets/maps with deterministic iteration order
  def makeSet[T] = new LinkedHashSet[T]
  def makeMap[K,V] : MMap[K,V]  = new LinkedHashMap[K,V]  
  
  // return immutable sets with/without deterministic iteration order
  val deterministic = false
  def makeISet[T] = if (deterministic) ListSet.empty[T] else Set.empty[T]
  
  // TODO: is this different from find?
  // variation of typical collectFirst. applies f to each element in t until
  // f produces a non-None value
  @annotation.tailrec 
  def collectFirst[A, B](t: Traversable[A], f: A => Option[B]): Option[B] = 
    if (t.isEmpty) None 
    else f(t.head) match {
      case None => collectFirst(t.tail, f)
      case found => found 
    }
  
  // combination of fold and find
  def foldUntil[A,B] (t : Traversable[A], acc : B, f : (B, A) => (B, Boolean)) : B = {
    @annotation.tailrec
    def foldUntilRec[A,B] (t : Traversable[A], acc : B, 
        f : (B, A) => (B, Boolean)) : B = 
      if (t.isEmpty) acc
      else (f(acc, t.head)) match {
        case (acc, true) => acc
        case (acc, false) => foldUntilRec(t.tail, acc, f)
      }
    foldUntilRec(t, acc, f)
  }  
  
  /** alternative to ++ */
  def combine[T] (l0 : List[T], l1 : List[T]) : List[T] = l0.foldLeft (l1) ((l0, t) => t :: l0) 
  
  /** update a map from K's to List[V]'s with the value v by adding v to the list found at k*/
  def updateLMap[K,V] (m : Map[K,List[V]], k : K, v : V) : Map[K,List[V]] = 
    m + (k -> (v :: m.getOrElse(k, List.empty[V])))
    
  /** update a map from K's to Set[V]'s with the value v by adding v to the list found at k*/
  def updateSMap[K,V] (m : Map[K,Set[V]], k : K, v : V) : Map[K,Set[V]] = 
    m + (k -> (m.getOrElse(k, Set.empty[V]) + v))

  /*
  def foldUntil[A,B] (lst : List[B], t : Traversable[A], transform : (List[B], A) => List[B], tst : A => Boolean) = {
    def foldUntilRec[A, B] (t : Traversable[A], lst : List[B], transform : (List[B], A) => List[B], tst : A => Boolean) =
        if (t.isEmpty) lst
        else if (tst(t.head)) transform(lst, t.head) else foldUntilRec(t.tail, lst transform, tst)
    foldUntil(tm ks)
  }
   */
  
  /** metaprogramming */
  //def makeWorklistAlgo[T](List[T])
  
  /** file I/O */
    
  /** @return Iterable of File's contained in @param dir (and subdirectories) filtered by @param f */
  def getAllFiles(dir : File, f : File => Boolean = RET_TRUE) : Iterable[File] = {
    require(dir.isDirectory())
    
    def listFilesRec(dirs : List[File], acc : List[File]) : List[File] = dirs match {
      case dir :: dirs => 
        val contents = dir.listFiles().toIterable
        listFilesRec(contents.foldLeft (dirs) ((dirs,file) => if (file.isDirectory) file :: dirs else dirs), 
                     contents.foldLeft (acc) ((acc, dir) => if (f(dir)) dir :: acc else acc))
      case Nil => acc
    }
    listFilesRec(List(dir), Nil)    
  }
  
  def deleteAllFiles(f : File) : Unit = {
    if (f.isDirectory) f.listFiles().foreach(f => deleteAllFiles(f))
    f.delete()    
  }
    
  /** logic */
  // a => b
  def implies(a : Boolean, b : Boolean) = !a || b
  
  /** implementation TODOS */
  def unimp(msg : String) = sys.error("Unimplemented: " + msg)
  
  /** hash code stuff */
  val PRIME = 37
 
  def makeHash(l : List[Any]) : Int = l.foldLeft (1) ((hash, ref) => hash * PRIME + ref.hashCode())
  
  /** strings and printing */
  def toCSVStr(l : Iterable[Any], sep : String = ", ") : String = 
    l.foldLeft ("") ((str, elem) => if (str.isEmpty()) elem.toString else s"$str$sep${elem.toString()}")
    
  /** converts *both* null and empty string to None, any other string to Some(str) */
  def strToOption(str : String) : Option[String] = if (str == null || str.isEmpty()) None else Some(str)
}
