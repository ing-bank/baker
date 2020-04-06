import sbt._
import Keys._
import sbtrelease.ReleasePlugin.autoImport._
import sbtrelease.ReleaseStateTransformations._
import xerial.sbt.Sonatype.SonatypeKeys._

object Publish {

  lazy val settings = if (sys.env.get("feedUrl").isDefined) AzureFeed else Sonatype

  val AzureFeed = Seq(
    credentials += Credentials(Path.userHome / ".sbt" / ".credentials"),
    publishTo := Some("BakeryOSSFeed" at sys.env.getOrElse("feedUrl", ""))
  )

  protected def isSnapshot(s: String) = s.trim endsWith "SNAPSHOT"

  protected val nexus = "https://oss.sonatype.org/"
  protected val ossSnapshots = "Sonatype OSS Snapshots" at nexus + "content/repositories/snapshots/"
  protected val ossStaging = "Sonatype OSS Staging" at nexus + "service/local/staging/deploy/maven2/"

  val Sonatype = Seq(
    sonatypeProfileName := "com.ing",
    licenses := Seq("MIT" -> url("https://opensource.org/licenses/MIT")),
    homepage := Some(url("https://github.com/ing-bank/baker")),
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