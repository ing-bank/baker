import sbt._
import Keys._
import xerial.sbt.Sonatype.SonatypeKeys._
import xerial.sbt.Sonatype.sonatypeCentralHost

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
    organization := "io.github.bekiroguz",
    credentials += Credentials(Path.userHome / ".credentials"),
    publishTo := Some("pkgs.dev.azure.com" at sys.env.getOrElse("FEEDURL", "")),
    publishMavenStyle := true,
    aetherDeploy / logLevel  := Level.Info
  )

  val ReleaseToSonatype = inThisBuild(List(
    organization := "io.github.bekiroguz",
    homepage := Some(url("https://github.com/bekiroguz/baker")),
    licenses := List(License.MIT),
    sonatypeCredentialHost := sonatypeCentralHost
  ))
}
