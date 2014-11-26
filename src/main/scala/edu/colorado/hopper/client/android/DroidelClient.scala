package edu.colorado.hopper.client.android

import java.io.File

import com.ibm.wala.ipa.modref.ModRef
import edu.colorado.droidel.driver.{AndroidAppTransformer, AndroidCGBuilder}
import edu.colorado.thresher.core.Options
import edu.colorado.walautil.WalaAnalysisResults

/** Base client for apps that have been preprocessed with Droidel */
abstract class DroidelClient(appPath : String,  androidLib : File) {

  val appTransformer = new AndroidAppTransformer(appPath, androidLib, droidelHome = Options.DROIDEL_HOME)
  // run Droidel on the app if it hasn't already been transformed
  if (!appTransformer.isAppDroidelProcessed()) {
    println("Processing app with Droidel")
    appTransformer.transformApp()
  } else println("App has already been Droidel-processed")

  lazy val walaRes = {
    val analysisScope = appTransformer.makeAnalysisScope(useHarness = true)
    new AndroidCGBuilder(analysisScope, appTransformer.harnessClassName, appTransformer.harnessMethodName)
    .makeAndroidCallGraph
  }

}
