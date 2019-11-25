import Dependencies.{scalaGraph, _}
import sbt.Keys._

def testScope(project: ProjectReference) = project % "test->test;test->compile"

val commonSettings = Defaults.coreDefaultSettings ++ Seq(
  organization := "com.ing.baker",
  scalaVersion := "2.12.4",
  crossScalaVersions := Seq("2.12.4"),
  fork := true,
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
  ),
  packageOptions in (Compile, packageBin) +=
    Package.ManifestAttributes(
      "Build-Time" -> new java.util.Date().toString,
      "Build-Commit" -> git.gitHeadCommit.value.getOrElse("No Git Revision Found")
    )
)

val dependencyOverrideSettings = Seq(
  // note that this does NOT add the dependencies, just forces the version
  dependencyOverrides ++= Seq(
    catsCore,
    akkaActor,
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

lazy val bakertypes = project.in(file("bakertypes"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-types",
    libraryDependencies ++= compileDeps(
      slf4jApi,
      ficusConfig,
      objenisis,
      scalapbRuntime,
      jodaTime,
      scalaReflect(scalaVersion.value)
    ) ++ testDeps(scalaTest, scalaCheck, logback, scalaCheck)
  )

lazy val intermediateLanguage = project.in(file("intermediate-language"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-intermediate-language",
    libraryDependencies ++= compileDeps(
      scalaGraph,
      slf4jApi,
      scalaGraphDot,
      objenisis,
      typeSafeConfig
    ) ++ testDeps(scalaTest, scalaCheck, logback)
  ).dependsOn(bakertypes)


lazy val runtime = project.in(file("runtime"))
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
        akkaCluster,
        akkaClusterSharding,
        akkaInmemoryJournal,
        akkaSlf4j,
        ficusConfig,
        catsCore,
        catsEffect,
        guava,
        chill,
        objenisis,
        scalapbRuntime,
        protobufJava,
        kryo,
        kryoSerializers,
        slf4jApi
      ) ++ testDeps(
        akkaStream,
        akkaTestKit,
        akkaMultiNodeTestkit,
        akkaStreamTestKit,
        akkaInmemoryJournal,
        akkaPersistenceCassandra,
        levelDB,
        levelDBJni,
        betterFiles,
        graphvizJava,
        junitInterface,
        scalaTest,
        scalaCheck,
        mockito,
        logback)
        ++ providedDeps(findbugs)
  )
  .dependsOn(intermediateLanguage, testScope(recipeDsl), testScope(recipeCompiler), testScope(bakertypes))
  .enablePlugins(MultiJvmPlugin)
  .configs(MultiJvm)

lazy val splitBrainResolver = project.in(file("split-brain-resolver"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-split-brain-resolver",
    // we have to exclude the sources because of a compiler bug: https://issues.scala-lang.org/browse/SI-10134
    sources in (Compile, doc) := Seq.empty,
    libraryDependencies ++=
      compileDeps(
        akkaActor,
        akkaCluster,
        akkaSlf4j,
        ficusConfig
      ) ++ testDeps(
        akkaTestKit,
        akkaMultiNodeTestkit,
        scalaTest
      ) ++ providedDeps(findbugs)
  )
  .enablePlugins(MultiJvmPlugin)
  .configs(MultiJvm)
  .settings(
//    logLevel := Level.Debug
  )

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
      compileDeps(slf4jApi) ++ testDeps(scalaTest, scalaCheck, logback, junitJupiter)
  )
  .dependsOn(recipeDsl, intermediateLanguage, testScope(recipeDsl))

lazy val baas = project.in(file("baas"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
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
  .dependsOn(recipeDsl, recipeCompiler, intermediateLanguage, runtime, testScope(runtime))

lazy val baker = project
  .in(file("."))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)
  .aggregate(bakertypes, runtime, recipeCompiler, recipeDsl, intermediateLanguage, splitBrainResolver, baas)

lazy val integration = project.in(file("integration"))
  .dependsOn(testScope(runtime))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)
  .settings(
    moduleName := "baker-integration",
    // we have to exclude the sources because of a compiler bug: https://issues.scala-lang.org/browse/SI-10134
    libraryDependencies ++=
      compileDeps(
        akkaActor,
        akkaCluster,
        akkaSlf4j
      ) ++ testDeps(
        akkaTestKit,
        akkaMultiNodeTestkit,
        betterFiles,
        scalaTest
      ) ++ providedDeps(findbugs)
  )
  .enablePlugins(MultiJvmPlugin)
  .configs(MultiJvm)

lazy val examples = project
  .in(file("examples"))
  .enablePlugins(JavaAppPackaging)
  .settings(commonSettings)
  .settings(noPublishSettings)
  .settings(
    moduleName := "examples",
    scalacOptions ++= Seq(
      "-Ypartial-unification"
    ),
    libraryDependencies ++=
      compileDeps(
        slf4jApi,
        slf4jSimple,
        http4s,
        http4sDsl,
        http4sServer,
        http4sCirce,
        circe,
        circeGeneric,
        kamon,
        kamonPrometheus,
        akkaPersistenceCassandra,
        akkaPersistenceQuery
      ) ++ testDeps(
        scalaTest,
        scalaCheck,
        junitInterface,
        slf4jApi,
        mockito,
        logback
      )
  )
  .settings(
    maintainer in Docker := "The Apollo Squad",
    packageSummary in Docker := "A web-shop checkout service example running baker",
    packageName in Docker := "apollo.docker.ing.net/baker-example-app",
    dockerExposedPorts := Seq(8080)
  )
  .dependsOn(bakertypes, runtime, recipeCompiler, recipeDsl, intermediateLanguage)
