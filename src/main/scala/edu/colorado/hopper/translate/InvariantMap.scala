package edu.colorado.hopper.translate

import com.twitter.util.LruMap
import InvariantMap._
import edu.colorado.hopper.state.Path

object InvariantMap {
  val DEBUG = false
  val USE_SUMMARIES = true // be careful! turning this off can lead to nontermination
  val MAX_SIZE = 1000
}

class InvariantMap[T](val invMap : LruMap[T,MinSet[Path]] = new LruMap[T,MinSet[Path]](MAX_SIZE)) { 
  
   /**
   * @return true if path @param p entails the weakest invariant at @param key
   * that is, returns true if the concretization of p \subseteq the concretization of the weakest invariant
   * otherwise, return false and update the weakest invariant at @param key with @param p
   */
  // TODO: figure out when to widen here. if a constraint has a smaller concretization, but no new path vars, we should widen...
  def pathEntailsInv(key : T, c : Path) : Boolean = {
    //println("inv contains key " + key + "? " + invMap.contains(key))
    val inv = invMap.getOrElse(key, new MinSet[Path])
    val newInv = inv + c.deepCopy
    if (DEBUG) println("inv was (size " + inv.size + ")" + inv + " newInv is " + newInv)
    if (newInv eq inv) {
      // if sums is unchanged after adding p, we know p |= sums
      if (DEBUG) {
        println("refuted by summary")
        println("refuting inv is " + inv)
      }
      USE_SUMMARIES // only allow refuting based on summary if USE_SUMMARIES is true
    } else {
      invMap.put(key, newInv)
      // TODO: make another copy here?      
      //if (!inv.isEmpty && c.maybeWiden(newInv)) {
        //invMap.put(key, MinSet.make(newInv.paths))
        //assert(pathEntailsInv(key, c))
        //false
        //pathEntailsInv(key, c)
      //}
      //else false // if adding p changed sums, we know p |\= sums
      false
    }
  }
  
  def clear() : Unit = invMap.clear
    
  override def clone : InvariantMap[T] = 
    new InvariantMap(new LruMap(InvariantMap.MAX_SIZE, invMap.clone.underlying.asInstanceOf[java.util.Map[T,MinSet[Path]]]))
  
}
//} else {
  //    invMap.put(key, newInv)
    //  false // if adding p changed sums, we know p |\= sums
    //}
  //}
    
  //override def clone : InvariantMap2 = 
    //new InvariantMap2(new LruMap(InvariantMap.MAX_SIZE, invMap.clone.underlying.asInstanceOf[java.util.Map[T,C]]))
///

/**
 * 
 * map from T (some kind of program point) to the weakest invariant 
 * (i.e. largest concretization) seen at T
 * 
 */
/*class InvariantMap[T](val invMap : LruMap[T,MinPathSet] = new LruMap[T,MinPathSet](100)) { 
  
   /**
   * @return true if path @param p entails the weakest invariant at @param key
   * that is, returns true if the concretization of p \subseteq the concretization of the weakest invariant
   * otherwise, return false and update the weakest invariant at @param key with @param p
   */
  def pathEntailsInv(key : T, p : Path) : Boolean = {
    val inv = invMap.getOrElse(key, new MinPathSet)
    val newInv = inv + p.deepCopy
    if (newInv eq inv) {
      if (InvariantMap.DEBUG) println("refuted by summary")
      true // if sums is unchanged after adding p, we know p |= sums
    } else {
      invMap.put(key, newInv)
      false // if adding p changed sums, we know p |\= sums
    }
  }
    
  override def clone : InvariantMap[T] = 
    new InvariantMap(new LruMap(InvariantMap.MAX_SIZE, invMap.clone.underlying.asInstanceOf[java.util.Map[T,MinPathSet]]))
}*/