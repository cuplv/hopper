package edu.colorado.scwala.util

import java.io.{File, FileInputStream, FileOutputStream, InputStream, OutputStream}
import java.util.jar.{JarEntry, JarFile, JarOutputStream}
import javax.tools.{DiagnosticCollector, JavaFileObject, ToolProvider}

import scala.collection.JavaConversions._

object JavaUtil {
  
  /** run javac
   *  @param classes - list of class names to compile *without* .java extension 
   *  @return true if compilation completed successfully, false otherwise */
  def compile(classes : Iterable[String], options : Iterable[String], printFailureDiagnostics : Boolean = true) : Boolean = {
    require(classes.forall(c => !c.endsWith(".java")))
    val compiler = ToolProvider.getSystemJavaCompiler()
    val diagnostics = new DiagnosticCollector[JavaFileObject]
    val fileMgr = compiler.getStandardFileManager(diagnostics, null, null)
    val compilationUnits = fileMgr.getJavaFileObjectsFromStrings(asJavaCollection(classes.map(_ + ".java")))    
    val task = compiler.getTask(null, fileMgr, diagnostics, asJavaIterable(options), null, compilationUnits)
    val res : Boolean = task.call()
    if (printFailureDiagnostics && !res) diagnostics.getDiagnostics().foreach(d => println(d)) 
    res
  }
  
  /** @param startInsideDir - if true, do not include @param dir in the paths of the JAR entries. otherwise,
   *  entries will all read dir/path/to/entry
   *  
   *  */
  def createJar(dir : File, jarName : String, rootPath : String, 
                startInsideDir : Boolean = false, filter : JarEntry => Boolean = Util.RET_TRUE) : File = {
    require(dir.exists(), s"Can't create JAR from nonexistent dir $dir")
    require(dir.isDirectory(), s"Can only create JAR from directory; found file $dir")    
    
    def addToJar(jarStream : JarOutputStream, file : File, reldir : String): Unit = {
      val fName = reldir + file.getName         
      val fNameMod = if (file.isDirectory) fName + "/" else fName
      val entry = new JarEntry(fNameMod)
      if (filter(entry)) {
        entry.setTime(file.lastModified)         
        if (file.isDirectory) {
          jarStream.putNextEntry(entry)
          jarStream.closeEntry()
          file.listFiles.foreach(i => addToJar(jarStream, i, fName + "/"))
        } else writeEntry(entry, new FileInputStream(file), jarStream)
      }
    }
    
    val outStream = new FileOutputStream(jarName)
    val jarStream = new JarOutputStream(outStream)
    
    if (startInsideDir) dir.listFiles.foreach(f => if (f.isDirectory()) addToJar(jarStream, f, rootPath))
    else addToJar(jarStream, dir, rootPath)
    
    jarStream.close()
    outStream.close()
    val outFile = new File(jarName)
    assert(outFile.exists())
    outFile
  }    
  
  private def writeEntry(e : JarEntry, entryStream : InputStream, jarStream : JarOutputStream) : Unit = {
    val buf = new Array[Byte](1024)
    jarStream.putNextEntry(e)
    Stream.continually(entryStream.read(buf)).takeWhile(_ != -1).foreach(jarStream.write(buf, 0, _))
    jarStream.closeEntry()
    entryStream.close()
  }
     
  /** Merge the input jars found in @param jarFiles into a single jar with name @param newJarName
   *  If two or more jars have duplicate entries, the first writer wins, and the other entry will not be added
   *  Note that this is an only an issue for duplicate file entries. duplicate directory entries simply
   *  mean that the directory with the given name is not added twice -- the contents of the given directory
   *  will be merged correctly
   *  
   *  @param duplicateWarning - if true, print warning message when a duplicate file entry is found and not added
   **/
  def mergeJars(jarFiles : Iterable[File], newJarName : String, duplicateWarning : Boolean = false) : Unit = {
    val outStream = new FileOutputStream(newJarName)
    val jarStream = new JarOutputStream(outStream)
    
    val jars = jarFiles.map(f => new JarFile(f))
    jars.foldLeft (Set.empty[String]) ((added, jar) => {
      jar.entries().foldLeft (added) ((added, e) => {
        val newAdded = added + e.getName()
        if (newAdded.size != added.size) writeEntry(e, jar.getInputStream(e), jarStream)
        else if (duplicateWarning && !e.isDirectory()) println(s"Duplicate entry $e; not adding")
        newAdded
      })
    }) 
       
    // cleanup
    jarStream.close()
    outStream.close()    
    jars.foreach(jar => jar.close())
  }
   
  // TODO: this is not very robust -- crashes unless the input Jar is nicely sorted so that directory
  // entries always occur before their children. probably better to just use the command line jar utility
  def extractJar(jarFile : File, outPath : String) : Unit = {
    def copyStream(istream : InputStream, ostream : OutputStream) : Unit = {
      val bytes =  new Array[Byte](1024)
      var len = -1
      while({ len = istream.read(bytes, 0, 1024); len != -1 })
        ostream.write(bytes, 0, len)
    }
    
    val basename = jarFile.getName.substring(0, jarFile.getName.lastIndexOf("."))
    val outDir = new File(outPath) //new File(file.getParentFile, basename)
    val jar = new JarFile(jarFile)
    val enu = jar.entries
    
    outDir.mkdirs()
    while (enu.hasMoreElements) {
      val entry = enu.nextElement
      val name = entry.getName
      val entryPath = 
        if(name.startsWith(basename)) name.substring(basename.length) 
        else name
        
      if (entry.isDirectory) new File(outDir, entryPath).mkdirs
      else {
        val istream = jar.getInputStream(entry)
        val ostream = new FileOutputStream(new File(outDir, entryPath))
        copyStream(istream, ostream)
        ostream.close
        istream.close
      }
    }
  }  
 
}