name := "Hopper"

version := "0.1"

organization := "University of Colorado Boulder"

scalaVersion := "2.10.2"

offline := true

scalacOptions ++= Seq("-deprecation", "-feature")

resolvers += "Local Maven Repository" at "file:///"+Path.userHome.absolutePath+"/.m2/repository"

resolvers += "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots"

libraryDependencies ++= Seq(
        "University of Colorado Boulder" %% "walautil" % "0.1-SNAPSHOT",
        "University of Colorado Boulder" %% "droidel" % "0.1-SNAPSHOT",
	"com.ibm.wala" % "com.ibm.wala.shrike" % "1.3.7-SNAPSHOT",
	"com.ibm.wala" % "com.ibm.wala.util" % "1.3.7-SNAPSHOT",
	"com.ibm.wala" % "com.ibm.wala.core" % "1.3.7-SNAPSHOT",
	"com.twitter" %% "util-collection" % "6.12.1",
	"com.squareup" % "javawriter" % "2.5.0")
