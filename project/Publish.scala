import sbt._
import Keys._
import xerial.sbt.Sonatype.SonatypeKeys._

object Publish {

  lazy val settings = 
    if (sys.env.contains("FEEDURL")) StableToAzureFeed
    else if ( (sys.env.contains("SONATYPE_USERNAME"))) ReleaseToSonatype
    else SuppressJavaDocs

  import aether.AetherKeys._

  val SuppressJavaDocs = Seq(
    doc / sources  := Seq(),
    packageDoc / publishArtifact  := false,
    packageSrc / publishArtifact  := true
  )

  val StableToAzureFeed = Seq(
    organization := "com.ing",
    credentials += Credentials(Path.userHome / ".credentials"),
    publishTo := Some("pkgs.dev.azure.com" at sys.env.getOrElse("FEEDURL", "")),
    publishMavenStyle := true,
    aetherDeploy / logLevel  := Level.Info
  )

  val ReleaseToSonatype = inThisBuild(List(
    organization := "com.ing",
    homepage := Some(url("https://github.com/ing-bank/baker")),
    licenses := List(License.MIT)
  )) 
}
