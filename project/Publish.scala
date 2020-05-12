import sbt._
import Keys._
import sbtrelease.ReleasePlugin.autoImport._
import sbtrelease.ReleaseStateTransformations._
import xerial.sbt.Sonatype.SonatypeKeys._

object Publish {

  lazy val settings =
    if (sys.env.contains("FEEDURL")) StableToAzureFeed
    else if ( (sys.env.contains("USERNAME"))) ReleaseToSonatype
    else SuppressJavaDocsAndSources

  import aether.AetherKeys._

  val SuppressJavaDocsAndSources = Seq(
    sources in doc := Seq(),
    publishArtifact in packageDoc := false,
    publishArtifact in packageSrc := false
  )

  val StableToAzureFeed = Seq(
    credentials += Credentials(Path.userHome / ".credentials"),
    publishTo := Some("pkgs.dev.azure.com" at sys.env.getOrElse("FEEDURL", "")),
    publishMavenStyle := true,
    logLevel in aetherDeploy := Level.Info
  )

  protected def isSnapshot(s: String) = s.trim endsWith "SNAPSHOT"

  protected val nexus = "https://oss.sonatype.org/"
  protected val ossSnapshots = "Sonatype OSS Snapshots" at nexus + "content/repositories/snapshots/"
  protected val ossStaging = "Sonatype OSS Staging" at nexus + "service/local/staging/deploy/maven2/"

  val ReleaseToSonatype = Seq(
    credentials ++= Seq(
      Credentials(
      "Sonatype Nexus Repository Manager",
      "oss.sonatype.org",
      sys.env.getOrElse("USERNAME", ""),
      sys.env.getOrElse("PASSWORD", "")
    ),
      Credentials(
        "GnuPG Key ID",
        "gpg",
        "303489A85EBB77F6E93E2A254CCF1479F92AE2B7", // key identifier
        "ignored" // this field is ignored; passwords are supplied by pinentry
      )
    ),
    sonatypeProfileName := "com.ing",
    licenses := Seq("MIT" -> url("https://opensource.org/licenses/MIT")),
    homepage := Some(url("https://github.com/ing-bank/baker")),
    scmInfo := Some(ScmInfo(
      browseUrl = url("https://github.com/ing-bank/baker"),
      connection = "scm:git@github.com:ing-bank/baker.git")),
    pomExtra := (
      <developers>
        <developer>
          <id>Apollo</id>
          <name>Squad Apollo</name>
        </developer>
      </developers>
    ),
    publishMavenStyle := true,
    publishTo := version((v: String) => Some(if (isSnapshot(v)) ossSnapshots else ossStaging)).value,
    publishArtifact in Test := false,
    pomIncludeRepository := (_ => false),
    releaseCrossBuild := true,
    releaseProcess := Seq[ReleaseStep](
      checkSnapshotDependencies,
      inquireVersions,
      runClean,
      runTest,
      setReleaseVersion,
      commitReleaseVersion,
      tagRelease,
      releaseStepCommandAndRemaining("+publishSigned"),
      setNextVersion,
      commitNextVersion,
      releaseStepCommand("sonatypeReleaseAll"),
      pushChanges
    )
  )
}