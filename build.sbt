import Dependencies._
import sbt.Keys._

val scalaV = "2.11.11"
val jvmV = "1.8"

val commonSettings = Defaults.coreDefaultSettings ++ Seq(
  organization := "com.ing.baker",
  scalaVersion := scalaV,
  scalacOptions := Seq("-unchecked", "-deprecation", "-encoding", "utf8", s"-target:jvm-$jvmV"),
  javacOptions := Seq("-source", jvmV, "-target", jvmV),
  fork in test := true,
  testOptions += Tests.Argument(TestFrameworks.JUnit, "-v"),
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

lazy val noPublishSettings = Seq(
  publish := (),
  publishLocal := (),
  publishArtifact := false
)

lazy val defaultModuleSettings = commonSettings ++ Revolver.settings ++ SonatypePublish.settings

lazy val scalaPBSettings = Seq(PB.targets in Compile := Seq(scalapb.gen() -> (sourceManaged in Compile).value))

lazy val petrinetApi = project.in(file("petrinet-api"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "petrinet-api",
    libraryDependencies ++= compileDeps(
      scalaGraph,
      catsCore,
      scalapbRuntime,
      slf4jApi,
      fs2Core) ++ testDeps(
      scalaCheck,
      scalaTest,
      mockito,
      logback
    )
  )

lazy val intermediateLanguage = project.in(file("intermediate-language"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "intermediate-language",
    libraryDependencies ++= compileDeps(
      slf4jApi,
      scalaGraphDot
    ) ++ testDeps(scalaTest, scalaCheck, logback)
  ).dependsOn(petrinetApi)

lazy val recipeRuntime = project.in(file("runtime"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  // The following settings are needed to depend on common petrinet proto messages, but not re-compile them.
  .settings(Seq(PB.protoSources in Compile += petrinetApi.base / "src/main/protobuf" ))
  .settings(Seq(excludeFilter in PB.generate := new SimpleFileFilter(
    (f: File) => f.getName.endsWith("common.proto") || f.getName.endsWith("petrinet-messages.proto")
  )))
  .settings(
    moduleName := "runtime",
    libraryDependencies ++=
      compileDeps(
        akkaActor,
        akkaPersistence,
        akkaPersistenceQuery,
        akkaClusterSharding,
        akkaDistributedData,
        akkaInmemoryJournal,
        akkaSlf4j,
        akkaStream,
        ficusConfig,
        guava,
        chill,
        scalapbRuntime,
        kryoSerializers,
        jodaTime,
        jodaConvert,
        slf4jApi
      ) ++ testDeps(
        akkaTestKit,
        akkaStreamTestKit,
        akkaInmemoryJournal,
        scalaTest,
        scalaCheck,
        mockito,
        logback)
        ++ providedDeps(findbugs)
  )
  .dependsOn(intermediateLanguage, petrinetApi)

lazy val recipeDsl = project.in(file("recipe-dsl"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "recipe-dsl",
    libraryDependencies ++=
      compileDeps(
        javaxInject,
        paranamer,
        scalaReflect
      ) ++
        testDeps(
          scalaTest,
          scalaCheck,
          junitInterface,
          slf4jApi,
          logback
        )
  )

lazy val recipeCompiler = project.in(file("compiler"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "compiler",
    libraryDependencies ++=
      compileDeps(slf4jApi) ++ testDeps(scalaTest, scalaCheck, logback)
  )
  .dependsOn(recipeDsl, intermediateLanguage, petrinetApi)

lazy val testModule = project.in(file("test-module"))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)
  .settings(
    moduleName := "test-module",
    libraryDependencies ++=
      testDeps(
        akkaSlf4j,
        akkaTestKit,
        logback,
        mockito,
        scalaTest,
        junitInterface,
        levelDB,
        levelDBJni,
        scalaCheck
      )
  )
  .dependsOn(recipeDsl, recipeCompiler, intermediateLanguage, recipeRuntime)

lazy val baker = project
  .in(file("."))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)
  .aggregate(petrinetApi, recipeRuntime, recipeCompiler, recipeDsl, intermediateLanguage, testModule)
