package edu.colorado.scwala.util

import scala.compat.Platform

// TODO: this is pretty ugly and Java-y
class Timer {
  private var elapsed = 0.0  
  private var started = 0.0  
  private var isStarted = false
  private var isStopped = true
  
  def printTimeTaken(task : String) = {
    stop
    println(s"$task took ${time}")
    clear
    start
  }
  
  def start() : Unit = {
    require(isStopped)
    started = Platform.currentTime
    isStarted = true
    isStopped = false
  }
  def stop() : Unit = {
    require(isStarted && !isStopped)
    elapsed += (Platform.currentTime - started)
    isStarted = false
    isStopped = true
  } 
  def clear() : Unit = {
    elapsed = 0.0
    isStarted = false
    isStopped = true
  }
  
  // get the elapsed time without stopping
  def curTimeSeconds : Double = {
    require(isStarted)
    (elapsed + (Platform.currentTime - started)) / 1000    
  }
  
  def time : Double = {
    require(isStopped)
    elapsed / 1000
  }
  
}
