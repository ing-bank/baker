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

lazy val `baker-interface` = project.in(file("baker-interface"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baker-interface",
    libraryDependencies ++= Seq(
      akkaActor,
      catsCore,
      scalaJava8Compat
    ) ++ providedDeps(findbugs)
  )
  .dependsOn(intermediateLanguage)

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
        akkaClusterTools,
        akkaDistributedData,
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
  .dependsOn(
    intermediateLanguage,
    `baker-interface`,
    `baas-protocol-interaction-scheduling`,
    `baas-protocol-recipe-event-publishing`,
    testScope(recipeDsl),
    testScope(recipeCompiler),
    testScope(bakertypes))
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

lazy val `baas-protocol-baker` = project.in(file("baas-protocol-baker"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baas-protocol-baker",
    libraryDependencies ++= Seq(
      akkaStream,
      akkaHttp
    )
  )
  .dependsOn(`baker-interface`)

lazy val `baas-protocol-interaction-scheduling` = project.in(file("baas-protocol-interaction-scheduling"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baas-protocol-interaction-scheduling"
  )
  .dependsOn(`baker-interface`)

lazy val `baas-protocol-recipe-event-publishing` = project.in(file("baas-protocol-recipe-event-publishing"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baas-protocol-recipe-event-publishing"
  )
  .dependsOn(`baker-interface`)

lazy val `baas-node-client` = project.in(file("baas-node-client"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baas-node-client",
    libraryDependencies ++= Seq(
      akkaStream,
      akkaHttp
    )
  )
  .dependsOn(`baker-interface`, `baas-protocol-baker`)

lazy val `baas-node-state` = project.in(file("baas-node-state"))
  .enablePlugins(JavaAppPackaging)
  .settings(commonSettings)
  .settings(
    moduleName := "baas-node-state",
    scalacOptions ++= Seq(
      "-Ypartial-unification"
    ),
    libraryDependencies ++= Seq(
      akkaHttp,
      akkaPersistenceCassandra,
      akkaManagementHttp,
      akkaClusterBoostrap,
      akkaDiscoveryKube
    )
  )
  .settings(
    maintainer in Docker := "The Apollo Squad",
    packageSummary in Docker := "The core node",
    packageName in Docker := "apollo.docker.ing.net/baas-node-state",
    dockerExposedPorts := Seq(8080)
  )
  .dependsOn(runtime, `baas-protocol-baker`, `baas-protocol-interaction-scheduling`)

lazy val `baas-node-interaction` = project.in(file("baas-node-interaction"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baas-node-interaction",
    libraryDependencies ++= Seq(
      akkaCluster,
      akkaClusterTools,
      slf4jApi
    )
  )
  .dependsOn(`baas-protocol-interaction-scheduling`, `baker-interface`)

lazy val `baas-node-event-listener` = project.in(file("baas-node-event-listener"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baas-node-event-listener",
    libraryDependencies ++= Seq(
      akkaCluster,
      akkaClusterTools,
      slf4jApi
    )
  )
  .dependsOn(`baas-protocol-recipe-event-publishing`, `baker-interface`)

lazy val `baas-tests` = project.in(file("baas-tests"))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)
  .settings(
    moduleName := "baas-tests",
    libraryDependencies ++= Seq() ++
      testDeps(
        akkaSlf4j,
        akkaTestKit,
        logback,
        scalaTest,
        junitInterface,
        levelDB,
        levelDBJni,
        scalaCheck
      )
  )
  .dependsOn(`baas-node-client`, `baas-node-state`, `baas-node-interaction`, `baas-node-event-listener`, recipeCompiler)
  .aggregate(`baas-node-client`, `baas-node-state`, `baas-node-interaction`, `baas-node-event-listener`)

lazy val baker = project.in(file("."))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)
  .aggregate(bakertypes, runtime, recipeCompiler, recipeDsl, intermediateLanguage, splitBrainResolver, `baas-tests`)

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

lazy val playground = project
  .in(file("playground"))
  .settings(
    name := "baker-playground",
    version := "0.1.0",
    organization := "com.ing.baker",
    scalaVersion := "2.12.4",
    libraryDependencies ++= Seq(
      "org.typelevel" %% "cats-effect" % "2.0.0",
      "dev.profunktor" %% "console4cats" % "0.8.0",
      "org.scalatest" %% "scalatest" % "3.0.8" % "test",
      "org.scalacheck" %% "scalacheck" % "1.14.1" % "test"
    ),
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

lazy val `baker-example` = project
  .in(file("examples/baker-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(commonSettings)
  .settings(noPublishSettings)
  .settings(
    moduleName := "baker-example",
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

lazy val `baas-client-example` = project
  .in(file("examples/baas-client-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(commonSettings)
  .settings(noPublishSettings)
  .settings(
    moduleName := "baas-client-example",
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
        circeGeneric
      ) ++ testDeps(
        scalaTest,
        scalaCheck
      )
  )
  .settings(
    maintainer in Docker := "The Apollo Squad",
    packageSummary in Docker := "A web-shop checkout service example running on baas",
    packageName in Docker := "apollo.docker.ing.net/baas-client-example",
    dockerExposedPorts := Seq(8080)
  )
  .dependsOn(bakertypes, `baas-node-client`, recipeCompiler, recipeDsl)

lazy val `baas-interactions-example` = project
  .in(file("examples/baas-interactions-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(commonSettings)
  .settings(noPublishSettings)
  .settings(
    moduleName := "baas-interactions-example",
    scalacOptions ++= Seq(
      "-Ypartial-unification"
    ),
    libraryDependencies ++=
      compileDeps(
        slf4jApi,
        slf4jSimple,
        catsEffect
      ) ++ testDeps(
        scalaTest,
        scalaCheck
      )
  )
  .settings(
    maintainer in Docker := "The Apollo Squad",
    packageSummary in Docker := "A web-shop checkout service interaction instances example running on baas",
    packageName in Docker := "apollo.docker.ing.net/baas-interactions-example",
    dockerExposedPorts := Seq(2551)
  )
  .dependsOn(`baas-node-interaction`)

lazy val `baas-event-listener-example` = project
  .in(file("examples/baas-event-listener-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(commonSettings)
  .settings(noPublishSettings)
  .settings(
    moduleName := "baas-event-listener-example",
    scalacOptions ++= Seq(
      "-Ypartial-unification"
    ),
    libraryDependencies ++=
      compileDeps(
        slf4jApi,
        slf4jSimple,
        catsEffect
      ) ++ testDeps(
        scalaTest,
        scalaCheck
      )
  )
  .settings(
    maintainer in Docker := "The Apollo Squad",
    packageSummary in Docker := "A web-shop checkout service interaction instances example running on baas",
    packageName in Docker := "apollo.docker.ing.net/baas-event-listener-example",
    dockerExposedPorts := Seq(2551)
  )
  .dependsOn(`baas-node-event-listener`)
