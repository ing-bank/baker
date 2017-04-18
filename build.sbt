import Dependencies._
import sbt.Keys._

val scalaV = "2.11.8"
val jvmV   = "1.8"

val commonSettings = Defaults.coreDefaultSettings ++ Seq(
    organization := "com.ing",
    scalaVersion := scalaV,
    scalacOptions := Seq("-unchecked", "-deprecation", "-encoding", "utf8", s"-target:jvm-$jvmV"),
    javacOptions := Seq("-source", jvmV, "-target", jvmV),
    fork in test := true,
    scalacOptions ++= Seq(
      "-unchecked",
      "-deprecation",
      "-feature",
      "-Ywarn-dead-code",
      "-language:higherKinds",
      "-language:existentials",
      "-language:postfixOps"
    )
  )

lazy val noPublishSettings = Seq(
  publish := (),
  publishLocal := (),
  publishArtifact := false
)

lazy val defaultModuleSettings = commonSettings ++ Revolver.settings ++ SonatypePublish.settings

lazy val baker = project.in(file("core"))
  .settings(defaultModuleSettings: _*)
  .settings(
    moduleName := "baker",
    libraryDependencies ++=
      compileDeps(
        kagera,
        kageraAkka,
        kageraVisualization,
        akkaPersistence,
        akkaActor,
        akkaCluster,
        akkaClusterSharding,
        scalaReflect,
        javaxInject,
        paranamer,
        typeSafeConfig,
        ficusConfig,
        akkaInmemoryJournal,
        guava,
        chill,
        kryoSerializers,
        jodaTime,
        jodaConvert,
        scalaXml,
        slf4jApi
      ) ++
      testDeps(
        akkaSlf4j,
        logback,
        mockito,
        scalaTest,
        junit,
        levelDB,
        levelDBJni
      ) ++
      providedDeps(
        findbugs
      ))

lazy val root = project
  .in(file("."))
  .aggregate(baker)
  .dependsOn(baker)
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)