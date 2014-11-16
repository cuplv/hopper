package edu.colorado.hopper.client.android

import java.io.File

import edu.colorado.droidel.driver.{AndroidAppTransformer, AndroidCGBuilder}
import edu.colorado.hopper.client.WalaAnalysisResults
import edu.colorado.thresher.core.Options

/** Base client for apps that have been preprocessed with Droidel */
abstract class DroidelClient(appPath : String,  androidLib : File) {

  val appTransformer = new AndroidAppTransformer(appPath, androidLib, droidelHome = Options.DROIDEL_HOME)
  // TODO: check if app has already been transformed, and perform transformation if not

  lazy val walaRes = {
    val analysisScope = appTransformer.makeAnalysisScope(useHarness = true)
    val _walaRes = new AndroidCGBuilder(analysisScope, appTransformer.harnessClassName, appTransformer.harnessMethodName)
                   .makeAndroidCallGraph
    // hacky due to code re-use across Droidel and Scwala
    new WalaAnalysisResults(_walaRes.cg, _walaRes.hg, _walaRes.hm, null)
  }

}
