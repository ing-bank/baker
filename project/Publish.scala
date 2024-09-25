import sbt._
import Keys._
import xerial.sbt.Sonatype.SonatypeKeys._

object Publish {

  lazy val settings = ReleaseToSonatype
  // lazy val settings = 
  //   if (sys.env.contains("FEEDURL")) StableToAzureFeed
  //   else if ( (sys.env.contains("SONATYPE_USERNAME"))) ReleaseToSonatype
  //   else SuppressJavaDocs

  import aether.AetherKeys._

  val SuppressJavaDocs = Seq(
    doc / sources  := Seq(),
    packageDoc / publishArtifact  := false,
    packageSrc / publishArtifact  := true
  )

  val StableToAzureFeed = Seq(
    organization := "com.ing.baker",
    credentials += Credentials(Path.userHome / ".credentials"),
    publishTo := Some("pkgs.dev.azure.com" at sys.env.getOrElse("FEEDURL", "")),
    publishMavenStyle := true,
    aetherDeploy / logLevel  := Level.Info
  )

  val ReleaseToSonatype = inThisBuild(List(
    organization := "com.ing.baker",
    homepage := Some(url("https://github.com/ing-bank/baker")),
    licenses := List(License.MIT)
  )) ++ List(
    sonatypeProfileName := "com.ing",
    pomExtra := (
      <developers>
        <developer>
          <id>Apollo</id>
          <name>Squad Apollo</name>
        </developer>
      </developers>
    )
  )
}
