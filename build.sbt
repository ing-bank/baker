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
  .settings(defaultModuleSettings ++ scalaPBSettings)
  .settings(
    moduleName := "petrinet-api",
    libraryDependencies ++= compileDeps(
      scalaGraph,
      catsCore,
      slf4jApi,
      fs2Core) ++ testDeps(
      scalaCheck,
      scalaTest,
      mockito,
      logback
    )
  )

lazy val petrinetAkka = project.in(file("petrinet-akka"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "petrinet-akka",
    libraryDependencies ++= compileDeps(
      akkaActor,
      akkaPersistence,
      akkaPersistenceQuery,
      akkaClusterSharding,
      akkaSlf4j,
      akkaStream) ++ testDeps(
      akkaInmemoryJournal,
      akkaTestKit,
      akkaStreamTestKit,
      scalaTest,
      mockito,
      logback
    )
  ).dependsOn(petrinetApi)

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
  .settings(
    moduleName := "runtime",
    libraryDependencies ++=
      compileDeps(
        akkaDistributedData,
        akkaInmemoryJournal,
        ficusConfig,
        guava,
        chill,
        kryoSerializers,
        jodaTime,
        jodaConvert,
        slf4jApi
      ) ++ testDeps(
        akkaTestKit,
        akkaStreamTestKit,
        scalaTest,
        scalaCheck,
        mockito,
        logback)
        ++ providedDeps(findbugs)
  )
  .dependsOn(intermediateLanguage, petrinetAkka)

lazy val recipeDsl = project.in(file("recipe-dsl"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "recipe-dsl",
    libraryDependencies ++=
      compileDeps(
        javaxInject,
        paranamer
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
  .aggregate(petrinetApi, petrinetAkka, recipeRuntime, recipeCompiler, recipeDsl, intermediateLanguage, testModule)
