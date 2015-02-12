package edu.colorado.hopper.client.android

import java.io.File

import edu.colorado.droidel.constants.DroidelConstants
import edu.colorado.droidel.driver.{AndroidAppTransformer, AndroidCGBuilder}
import edu.colorado.droidel.preprocessor.ApkDecoder
import edu.colorado.thresher.core.Options
import edu.colorado.walautil.Timer

/** Base client for apps to be preocessed with Droidel */
abstract class DroidelClient(appPath : String, androidLib : File, useJPhantom : Boolean = true,
                             appBinSuffix : String = DroidelConstants.BIN_SUFFIX) {

  val appTransformer = {
    val appFile = new File(appPath)
    val droidelInput =
      if (appFile.isFile())
        // decode the app resources and decompile the dex bytecodes to Java bytecodes
        new ApkDecoder(appPath, droidelHome = Options.DROIDEL_HOME).decodeApp.getAbsolutePath()
      else appPath

    val appTransformer =
      new AndroidAppTransformer(droidelInput, androidLib, droidelHome = Options.DROIDEL_HOME, useJPhantom = useJPhantom,
                                instrumentLibs = false, cleanupGeneratedFiles = true,
                                generateFrameworkIndependentHarness = false)
    // run Droidel on the app if it hasn't already been transformed
    if (!appTransformer.isAppDroidelProcessed()) {
      println("Processing app with Droidel")
      appTransformer.transformApp()
    } else println("App has already been Droidel-processed")
    appTransformer
  }



  val (walaRes, analysisCache) = {
    val analysisScope = appTransformer.makeAnalysisScope(useHarness = true)
    val timer = new Timer
    timer.start()
    println("Building call graph")
    val cgBuilder =
      new AndroidCGBuilder(analysisScope, appTransformer.harnessClassName, appTransformer.harnessMethodName)
    val res = cgBuilder.makeAndroidCallGraph
    timer.printTimeTaken("Building call graph")
    (res, cgBuilder.cache)
  }

}
