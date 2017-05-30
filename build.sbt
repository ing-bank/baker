import Dependencies._
import sbt.Keys._

val scalaV = "2.11.8"
val jvmV   = "1.8"

val commonSettings = Defaults.coreDefaultSettings ++ Seq(
    organization := "com.ing.baker",
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
      "-language:implicitConversions",
      "-language:postfixOps",
      "-Xfatal-warnings"
    )
  )

val allLibraries =
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
    )

lazy val noPublishSettings = Seq(
  publish := (),
  publishLocal := (),
  publishArtifact := false
)

lazy val defaultModuleSettings = commonSettings ++ Revolver.settings ++ SonatypePublish.settings

lazy val compiledRecipe = project.in(file("compiledRecipe"))
  .settings(defaultModuleSettings: _*)
  .settings(
    moduleName := "compiledRecipe",
    libraryDependencies ++= allLibraries
  )

lazy val runtime = project.in(file("runtime"))
  .settings(defaultModuleSettings: _*)
  .settings(
    moduleName := "runtime",
    libraryDependencies ++= allLibraries
  )
  .dependsOn(compiledRecipe)

lazy val compiler = project.in(file("compiler"))
  .settings(defaultModuleSettings: _*)
  .settings(
    moduleName := "compiler",
    libraryDependencies ++= allLibraries
  )
  .dependsOn(recipedsl, compiledRecipe)

lazy val recipedsl = project.in(file("recipedsl"))
  .settings(defaultModuleSettings: _*)
  .settings(
    moduleName := "recipedsl",
    libraryDependencies ++= allLibraries
  )

lazy val testModule = project.in(file("testModule"))
  .settings(defaultModuleSettings: _*)
  .settings(
    moduleName := "testModule",
    libraryDependencies ++= allLibraries
  )
  .dependsOn(recipedsl, runtime, compiler, compiledRecipe)

lazy val root = project
  .in(file("."))
  .aggregate(runtime, compiler, recipedsl, compiledRecipe, testModule)
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)