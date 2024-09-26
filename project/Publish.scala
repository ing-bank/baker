import sbt._
import Keys._
import xerial.sbt.Sonatype.SonatypeKeys._
import sbtdynver.DynVerPlugin.autoImport._

object Publish {

  lazy val settings = 
    if (sys.env.contains("AZURE_FEEDURL")) PublishToAzure
    else if ( (sys.env.contains("SONATYPE_USERNAME"))) ReleaseToSonatype
    else SuppressJavaDocs

  import aether.AetherKeys._

  val SuppressJavaDocs = Seq(
    doc / sources  := Seq(),
    packageDoc / publishArtifact  := false,
    packageSrc / publishArtifact  := true
  )

  val PublishToAzure = inThisBuild(List(
        dynverSeparator := "-"
  )) ++ List(
    credentials += Credentials(Path.userHome / ".credentials"),
    publishTo := Some("pkgs.dev.azure.com" at sys.env.getOrElse("AZURE_FEEDURL", "")),
    publishMavenStyle := true
  )

  val ReleaseToSonatype = inThisBuild(List(
    homepage := Some(url("https://github.com/ing-bank/baker")),
    licenses := List(License.MIT),
    dynverSeparator := "-",
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
