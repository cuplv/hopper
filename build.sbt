name := "Hopper"

version := "0.1"

organization := "University of Colorado Boulder"

scalaVersion := "2.10.2"

resolvers += "Local Maven Repository" at "file:///"+Path.userHome.absolutePath+"/.m2/repository"

libraryDependencies ++= Seq(
        "University of Colorado Boulder" %% "droidel" % "0.1-SNAPSHOT",
	"com.ibm.wala" % "com.ibm.wala.shrike" % "1.3.4-SNAPSHOT",
	"com.ibm.wala" % "com.ibm.wala.util" % "1.3.4-SNAPSHOT",
	"com.ibm.wala" % "com.ibm.wala.core" % "1.3.4-SNAPSHOT",
	"com.twitter" %% "util-collection" % "6.12.1",
	"com.squareup" % "javawriter" % "2.5.0")

EclipseKeys.createSrc := EclipseCreateSrc.Default + EclipseCreateSrc.Resource

EclipseKeys.withSource := true