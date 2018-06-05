import Dependencies._
import sbt.Keys._

def testScope(project: ProjectReference) = project % "test->test;test->compile"

val commonSettings = Defaults.coreDefaultSettings ++ Seq(
  organization := "com.ing.baker",
  scalaVersion := "2.12.4",
  crossScalaVersions := Seq("2.11.12", "2.12.4"),
  fork in test := true,
  testOptions += Tests.Argument(TestFrameworks.JUnit, "-v"),
  javacOptions := Seq("-source", jvmV, "-target", jvmV),
  scalacOptions := Seq(
    "-unchecked",
    "-deprecation",
    "-feature",
    "-Ywarn-dead-code",
    "-language:higherKinds",
    "-language:existentials",
    "-language:implicitConversions",
    "-language:postfixOps",
    "-encoding", "utf8",
    s"-target:jvm-$jvmV",
    "-Xfatal-warnings"
  )
)

val dependencyOverrideSettings = Seq(
  // note that this does NOT add the dependencies, just forces the version
  dependencyOverrides ++= Seq(
    catsCore,
    akkaActor,
    akkaStream,
    "com.github.jnr" % "jnr-constants" % "0.9.9"
  )
)

lazy val noPublishSettings = Seq(
  publish := {},
  publishLocal := {},
  publishArtifact := false
)

lazy val defaultModuleSettings = commonSettings ++ dependencyOverrideSettings ++ Revolver.settings ++ SonatypePublish.settings

lazy val scalaPBSettings = Seq(PB.targets in Compile := Seq(scalapb.gen() -> (sourceManaged in Compile).value))

lazy val petrinetApi = project.in(file("petrinet-api"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "petrinet-api",
    libraryDependencies ++= compileDeps(
      scalaGraph,
      catsCore,
      catsEffect,
      scalapbRuntime,
      slf4jApi,
      kryo
      ) ++ testDeps(
      scalaCheck,
      scalaTest,
      mockito,
      logback
    )
  )


lazy val bakertypes = project.in(file("bakertypes"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-types",
    libraryDependencies ++= compileDeps(
      slf4jApi,
      objenisis,
      jodaTime,
      scalaReflect(scalaVersion.value)
    ) ++ testDeps(scalaTest, scalaCheck, logback)
  )

lazy val intermediateLanguage = project.in(file("intermediate-language"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-intermediate-language",
    libraryDependencies ++= compileDeps(
      slf4jApi,
      scalaGraphDot,
      graphvizJava,
      objenisis,
      jodaTime
    ) ++ testDeps(scalaTest, scalaCheck, logback)
  ).dependsOn(petrinetApi, bakertypes)


lazy val recipeRuntime = project.in(file("runtime"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baker-runtime",
    // we have to exclude the sources because of a compiler bug: https://issues.scala-lang.org/browse/SI-10134
    sources in (Compile, doc) := Seq.empty,
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
        objenisis,
        scalapbRuntime,
        kryoSerializers,
        protobufJava,
        jodaTime,
        jodaConvert,
        slf4jApi
      ) ++ testDeps(
        akkaTestKit,
        akkaStreamTestKit,
        akkaInmemoryJournal,
        junitInterface,
        scalaTest,
        scalaCheck,
        mockito,
        logback)
        ++ providedDeps(findbugs)
  )
  .dependsOn(intermediateLanguage, petrinetApi, testScope(recipeDsl), testScope(recipeCompiler))

lazy val recipeDsl = project.in(file("recipe-dsl"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-recipe-dsl",
    // we have to exclude the sources because of a compiler bug: https://issues.scala-lang.org/browse/SI-10134
    sources in (Compile, doc) := Seq.empty,
    libraryDependencies ++=
      compileDeps(
        javaxInject,
        paranamer,
        scalaReflect(scalaVersion.value),
        jodaTime
      ) ++
        testDeps(
          scalaTest,
          scalaCheck,
          junitInterface,
          slf4jApi,
          logback
        )
  ).dependsOn(bakertypes)

lazy val recipeCompiler = project.in(file("compiler"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-compiler",
    libraryDependencies ++=
      compileDeps(slf4jApi) ++ testDeps(scalaTest, scalaCheck, logback)
  )
  .dependsOn(recipeDsl, intermediateLanguage, petrinetApi)

lazy val baas = project.in(file("baas"))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)
  .settings(
    moduleName := "baker-baas",
    libraryDependencies ++=
      compileDeps(
        akkaHttp,
        akkaPersistenceCassandra) ++
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
  .dependsOn(testScope(recipeDsl), recipeCompiler, intermediateLanguage, testScope(recipeRuntime), baas)

lazy val baker = project
  .in(file("."))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)
  .aggregate(bakertypes, petrinetApi, recipeRuntime, recipeCompiler, recipeDsl, intermediateLanguage, testModule)
