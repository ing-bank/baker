import sbt._
import Keys._
import xerial.sbt.Sonatype.SonatypeKeys._
import sbtdynver.DynVerPlugin.autoImport._

object Publish {

  lazy val settings = 
    if (sys.env.contains("AZURE_FEEDURL")) PublishToAzure
    else if ( (sys.env.contains("SONATYPE_USERNAME"))) PublishToSonatype
    else SuppressJavaDocs

  import aether.AetherKeys._

  val SuppressJavaDocs = Seq(
    doc / sources  := Seq(),
    packageDoc / publishArtifact  := false,
    packageSrc / publishArtifact  := true
  )

  // aetherDeploy will deploy to the Azure Artifacts repository
  val PublishToAzure = inThisBuild(List(
    dynverSeparator := "-",
    version := version.value.replace("-SNAPSHOT", ""),
  )) ++ List(
    credentials += Credentials(
      "Azure Artifacts",
      "pkgs.dev.azure.com",
      sys.env.getOrElse("AZURE_FEEDUSER", ""),
      sys.env.getOrElse("AZURE_FEEDPASSWORD", "")
    ),
    publishTo := Some("Azure Artifacts" at sys.env.getOrElse("AZURE_FEEDURL", "")),
    publishMavenStyle := true,
    sonatypeCredentialHost := ""
  )

  // ci-release will deploy to the Sonatype repository
  val PublishToSonatype = inThisBuild(List(
    homepage := Some(url("https://github.com/ing-bank/baker")),
    licenses := List(License.MIT),
    dynverSeparator := "-",
    version := version.value.replace("-SNAPSHOT", ""),
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
