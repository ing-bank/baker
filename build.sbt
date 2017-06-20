import Dependencies._
import sbt.Keys._

val scalaV = "2.11.8"
val jvmV = "1.8"

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

lazy val noPublishSettings = Seq(
  publish := (),
  publishLocal := (),
  publishArtifact := false
)

lazy val defaultModuleSettings = commonSettings ++ Revolver.settings ++ SonatypePublish.settings

lazy val intermediateLanguage = project.in(file("intermediate-language"))
  .settings(defaultModuleSettings: _*)
  .settings(
    moduleName := "intermediate-language",
    libraryDependencies ++= compileDeps(
      kagera,
      kageraVisualization,
      slf4jApi
    ) ++ testDeps(scalaTest)
  )

lazy val runtime = project.in(file("runtime"))
  .settings(defaultModuleSettings: _*)
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
      ) ++ testDeps(scalaTest)
        ++ providedDeps(findbugs)
  )
  .dependsOn(intermediateLanguage)

lazy val compiler = project.in(file("compiler"))
  .settings(defaultModuleSettings: _*)
  .settings(
    moduleName := "compiler",
    libraryDependencies ++=
      compileDeps(slf4jApi) ++ testDeps(scalaTest)
  )
  .dependsOn(recipedsl, intermediateLanguage)

lazy val recipedsl = project.in(file("recipe-dsl"))
  .settings(defaultModuleSettings: _*)
  .settings(
    moduleName := "recipe-dsl",
    libraryDependencies ++=
      compileDeps(
        javaxInject,
        paranamer
      ) ++
        testDeps(
          scalaTest,
          junitInterface
        )
  )

lazy val testModule = project.in(file("test-module"))
  .settings(defaultModuleSettings: _*)
  .settings(
    moduleName := "test-module",
    libraryDependencies ++=
      testDeps(
        akkaSlf4j,
        logback,
        mockito,
        scalaTest,
        junitInterface,
        levelDB,
        levelDBJni
      )
  )
  .dependsOn(recipedsl, compiler, intermediateLanguage, runtime)

lazy val root = project
  .in(file("."))
  .aggregate(runtime, compiler, recipedsl, intermediateLanguage, testModule)
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)