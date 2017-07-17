import Dependencies.{scalaCheck, _}
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

lazy val intermediateLanguage = project.in(file("intermediate-language"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "intermediate-language",
    libraryDependencies ++= compileDeps(
      kagera,
      kageraVisualization,
      slf4jApi
    ) ++ testDeps(scalaTest, scalaCheck)
  )

lazy val runtime = project.in(file("runtime"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "runtime",
    libraryDependencies ++=
      compileDeps(
        kageraAkka,
        akkaDistributedData,
        akkaInmemoryJournal,
        ficusConfig,
        guava,
        chill,
        kryoSerializers,
        jodaTime,
        jodaConvert,
        slf4jApi
      ) ++ testDeps(scalaTest, scalaCheck)
        ++ providedDeps(findbugs)
  )
  .dependsOn(intermediateLanguage)

lazy val compiler = project.in(file("compiler"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "compiler",
    libraryDependencies ++=
      compileDeps(slf4jApi) ++ testDeps(scalaTest, scalaCheck)
  )
  .dependsOn(recipedsl, intermediateLanguage)

lazy val recipedsl = project.in(file("recipe-dsl"))
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
          junitInterface
        )
  )

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
  .dependsOn(recipedsl, compiler, intermediateLanguage, runtime)

lazy val root = project
  .in(file("."))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)
  .aggregate(runtime, compiler, recipedsl, intermediateLanguage, testModule)
