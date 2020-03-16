import Dependencies._
import sbt.Keys._

def testScope(project: ProjectReference): ClasspathDep[ProjectReference] = project % "test->test;test->compile"

lazy val buildExampleDockerCommand: Command = Command.command("buildExampleDocker")({
  state =>
    val extracted = Project.extract(state)
    val currentVersion = extracted.get(version in ThisBuild)

    "baas-node-state/docker:publishLocal" ::
      "baas-client-example/docker:publishLocal" ::
      "baas-event-listener-example/docker:publishLocal" ::
      "baas-baker-event-listener-example/docker:publishLocal" ::
      "bakery-controller/docker:publishLocal" ::
      "project baas-interaction-example-make-payment" ::
      "buildInteractionDockerImage docker:publishLocal webshop.webservice.MakePaymentInstance" ::
      "project baas-interaction-example-ship-items" ::
      "buildInteractionDockerImage docker:publishLocal webshop.webservice.ShipItemsInstance" ::
      "project baas-interaction-example-reserve-items" ::
      "buildInteractionDockerImage docker:publishLocal webshop.webservice.ReserveItemsInstance" ::
      "project baas-smoke-tests" ::
      state
})

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
  coverageExcludedPackages := "<empty>;.*.javadsl;.*.scaladsl;.*.common;.*.protobuf",
  packageOptions in(Compile, packageBin) +=
    Package.ManifestAttributes(
      "Build-Time" -> new java.util.Date().toString,
      "Build-Commit" -> git.gitHeadCommit.value.getOrElse("No Git Revision Found")
    )
)

val dependencyOverrideSettings = Seq(
  dependencyOverrides ++= Seq(
    catsCore,
    akkaActor,
    jnrConstants
  )
)

lazy val noPublishSettings = Seq(
  publish := {},
  publishLocal := {},
  publishArtifact := false
)

lazy val defaultModuleSettings = commonSettings ++ dependencyOverrideSettings ++ SonatypePublish.settings

lazy val scalaPBSettings = Seq(PB.targets in Compile := Seq(scalapb.gen() -> (sourceManaged in Compile).value))

lazy val bakertypes = project.in(file("bakertypes"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-types",
    libraryDependencies ++= compileDeps(
      slf4jApi,
      objenisis,
      scalapbRuntime,
      jodaTime,
      typeSafeConfig,
      scalaReflect(scalaVersion.value),
      scalaLogging
    ) ++ testDeps(scalaTest, scalaCheck, scalaCheck)
  )

lazy val intermediateLanguage = project.in(file("intermediate-language"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-intermediate-language",
    libraryDependencies ++= compileDeps(
      scalaGraph,
      slf4jApi,
      scalaGraphDot,
      typeSafeConfig,
      scalaLogging
    ) ++ testDeps(scalaTest, scalaCheck)
  ).dependsOn(bakertypes)

lazy val `baker-interface` = project.in(file("baker-interface"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baker-interface",
    libraryDependencies ++= Seq(
      catsEffect,
      scalaJava8Compat
    ) ++ providedDeps(findbugs) ++ testDeps(
      scalaTest
    )
  )
  .dependsOn(intermediateLanguage)

lazy val runtime = project.in(file("runtime"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baker-runtime",
    // we have to exclude the sources because of a compiler bug: https://issues.scala-lang.org/browse/SI-10134
    sources in(Compile, doc) := Seq.empty,
    libraryDependencies ++=
      compileDeps(
        akkaActor,
        akkaPersistence,
        akkaPersistenceQuery,
        akkaCluster,
        akkaClusterTools,
        akkaDistributedData,
        akkaClusterSharding,
        akkaBoostrap,
        akkaSlf4j,
        akkaInmemoryJournal,
        ficusConfig,
        catsCore,
        catsEffect,
        scalapbRuntime,
        protobufJava,
        slf4jApi,
        scalaLogging
      ) ++ testDeps(
        akkaStream,
        akkaTestKit,
        akkaMultiNodeTestkit,
        akkaStreamTestKit,
        akkaPersistenceCassandra,
        levelDB,
        levelDBJni,
        betterFiles,
        graphvizJava,
        junitInterface,
        scalaTest,
        scalaCheck,
        mockito)
        ++ providedDeps(findbugs)
  )
  .dependsOn(
    intermediateLanguage,
    `baker-interface`,
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
    sources in(Compile, doc) := Seq.empty,
    libraryDependencies ++=
      compileDeps(
        akkaActor,
        akkaCluster,
        ficusConfig,
        slf4jApi,
        scalaLogging
      ) ++ testDeps(
        akkaTestKit,
        akkaMultiNodeTestkit,
        scalaTest
      )
  )
  .enablePlugins(MultiJvmPlugin)
  .configs(MultiJvm)

lazy val recipeDsl = project.in(file("recipe-dsl"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-recipe-dsl",
    // we have to exclude the sources because of a compiler bug: https://issues.scala-lang.org/browse/SI-10134
    sources in(Compile, doc) := Seq.empty,
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
          slf4jApi
        )
  ).dependsOn(bakertypes)

lazy val recipeCompiler = project.in(file("compiler"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-compiler",
    libraryDependencies ++=
      testDeps(scalaTest, scalaCheck, junitJupiter)
  )
  .dependsOn(recipeDsl, intermediateLanguage, testScope(recipeDsl))

lazy val `baas-protocol-baker` = project.in(file("baas-protocol-baker"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baas-protocol-baker",
    libraryDependencies ++= Seq(
      http4s,
      http4sDsl
    )
  )
  .dependsOn(`baker-interface`)

lazy val `baas-protocol-interaction-scheduling` = project.in(file("baas-protocol-interaction-scheduling"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baas-protocol-interaction-scheduling",
    libraryDependencies ++= Seq(
      http4s,
      http4sDsl,
      http4sClient
    )
  )
  .dependsOn(`baker-interface`)

lazy val `baas-protocol-recipe-event-publishing` = project.in(file("baas-protocol-recipe-event-publishing"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baas-protocol-recipe-event-publishing",
    libraryDependencies ++= Seq(
      http4s,
      http4sDsl,
      http4sClient
    )
  )
  .dependsOn(`baker-interface`)

lazy val `baas-protocol-baker-event-publishing` = project.in(file("baas-protocol-baker-event-publishing"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baas-protocol-baker-event-publishing",
    libraryDependencies ++= Seq(
      http4s,
      http4sDsl,
      http4sClient
    )
  )
  .dependsOn(`baker-interface`)

lazy val `baas-node-client` = project.in(file("baas-node-client"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baas-node-client",
    libraryDependencies ++= Seq(
      http4s,
      http4sDsl,
      http4sClient
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
      slf4jApi,
      slf4jSimple,
      akkaPersistenceCassandra,
      akkaManagementHttp,
      akkaClusterBoostrap,
      akkaDiscoveryKube,
      skuber,
      http4s,
      http4sDsl,
      http4sServer
    ) ++ testDeps(
      slf4jApi,
      slf4jSimple,
      logback,
      scalaTest,
      mockServer,
      circe,
      circeGeneric
    )
  )
  .settings(
    maintainer in Docker := "The Bakery Team",
    packageSummary in Docker := "The core node",
    packageName in Docker := "baas-node-state",
    dockerRepository in Docker := sys.env.get("BAAS_DOCKER_REPO")
  )
  .dependsOn(
    runtime,
    `baas-node-client`,
    `baas-protocol-baker`,
    `baas-protocol-interaction-scheduling`,
    `baas-protocol-recipe-event-publishing`,
    `baas-protocol-baker-event-publishing`,
    recipeCompiler, recipeDsl, intermediateLanguage
  )

lazy val `baas-node-interaction` = project.in(file("baas-node-interaction"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baas-node-interaction",
    libraryDependencies ++= Seq(
      slf4jApi,
      slf4jSimple,
      http4s,
      http4sDsl,
      http4sServer
    ) ++ testDeps(
      scalaTest,
      logback
    )
  )
  .dependsOn(`baas-protocol-interaction-scheduling`, `baker-interface`)

lazy val `baas-node-event-listener` = project.in(file("baas-node-event-listener"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baas-node-event-listener",
    libraryDependencies ++= Seq(
      slf4jApi,
      slf4jSimple,
      http4s,
      http4sDsl,
      http4sServer
    ) ++ testDeps(
      scalaTest,
      logback
    ))
  .dependsOn(`baas-protocol-recipe-event-publishing`, `baker-interface`)

lazy val `baas-node-baker-event-listener` = project.in(file("baas-node-baker-event-listener"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baas-node-baker-event-listener",
    libraryDependencies ++= Seq(
      slf4jApi,
      slf4jSimple,
      http4s,
      http4sDsl,
      http4sServer
    ) ++ testDeps(
      scalaTest,
      logback
    )
  )
  .dependsOn(`baas-protocol-baker-event-publishing`, `baker-interface`)

lazy val `bakery-controller` = project.in(file("bakery-controller"))
  .settings(defaultModuleSettings)
  .enablePlugins(JavaAppPackaging)
  .settings(
    maintainer in Docker := "The Bakery Team",
    packageSummary in Docker := "The bakery controller",
    packageName in Docker := "bakery-controller",
    dockerRepository in Docker := sys.env.get("BAAS_DOCKER_REPO")
  )
  .settings(
    moduleName := "bakery-controller",
    libraryDependencies ++= Seq(
      slf4jApi,
      slf4jSimple,
      scalaLogging,
      skuber,
      http4s,
      http4sDsl,
      http4sServer
    ) ++ testDeps(
      scalaTest,
      logback
    )
  )
  .dependsOn(bakertypes, recipeCompiler, recipeDsl, intermediateLanguage, `baas-node-client`)
  .aggregate(bakertypes, recipeCompiler, recipeDsl, intermediateLanguage, `baas-node-client`)

lazy val baker = project.in(file("."))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)
  .aggregate(bakertypes, runtime, recipeCompiler, recipeDsl, intermediateLanguage, splitBrainResolver,
    `baas-node-client`, `baas-node-state`, `baas-node-interaction`, `baas-node-event-listener`,
    `baas-node-baker-event-listener`, `sbt-baas-docker-generate`, `baas-protocol-interaction-scheduling`,
    `baker-interface`)

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
        mockito
      )
  )
  .settings(
    maintainer in Docker := "The Bakery Team",
    packageSummary in Docker := "A web-shop checkout service example running baker",
    packageName in Docker := "baker-example-app",
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
    maintainer in Docker := "The Bakery Team",
    packageSummary in Docker := "A web-shop checkout service example running on baas",
    packageName in Docker := "baas-client-example",
    dockerRepository in Docker := sys.env.get("BAAS_DOCKER_REPO")
  )
  .dependsOn(bakertypes, `baas-node-client`, recipeCompiler, recipeDsl)

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
        http4s,
        http4sDsl,
        http4sServer,
      ) ++ testDeps()
  )
  .settings(
    maintainer in Docker := "The Bakery Team",
    packageSummary in Docker := "A web-shop checkout service example running on baas",
    packageName in Docker := "baas-event-listener-example",
    dockerRepository in Docker := sys.env.get("BAAS_DOCKER_REPO")
  )
  .dependsOn(`baas-node-event-listener`)

lazy val `baas-baker-event-listener-example` = project
  .in(file("examples/baas-baker-event-listener-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(commonSettings)
  .settings(noPublishSettings)
  .settings(
    moduleName := "baas-baker-event-listener-example",
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
      ) ++ testDeps()
  )
  .settings(
    maintainer in Docker := "The Bakery Team",
    packageSummary in Docker := "A web-shop checkout service example running on baas",
    packageName in Docker := "baas-baker-event-listener-example",
    dockerRepository in Docker := sys.env.get("BAAS_DOCKER_REPO")
  )
  .dependsOn(`baas-node-baker-event-listener`)

lazy val `baas-interaction-example-reserve-items` = project.in(file("examples/baas-interaction-examples/reserve-items"))
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(baas.sbt.BuildInteractionDockerImageSBTPlugin)
  .settings(commonSettings)
  .settings(
    moduleName := "baas-interaction-example-reserve-items",
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
  .dependsOn(`baas-node-interaction`)

lazy val `baas-interaction-example-ship-items` = project.in(file("examples/baas-interaction-examples/ship-items"))
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(baas.sbt.BuildInteractionDockerImageSBTPlugin)
  .settings(commonSettings)
  .settings(
    moduleName := "baas-interaction-example-ship-items",
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
  .dependsOn(`baas-node-interaction`)

lazy val `baas-interaction-example-make-payment` = project.in(file("examples/baas-interaction-examples/make-payment"))
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(baas.sbt.BuildInteractionDockerImageSBTPlugin)
  .settings(commonSettings)
  .settings(
    moduleName := "baas-interaction-example-make-payment",
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
  .dependsOn(`baas-node-interaction`)

lazy val `baas-smoke-tests` = project.in(file("baas-smoke-tests"))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)
  .settings(
    moduleName := "baas-smoke-tests",
    commands += buildExampleDockerCommand,
    libraryDependencies ++= Seq() ++
      testDeps(
        http4sDsl,
        http4sClient,
        circe,
        slf4jApi,
        slf4jSimple,
        scalaTest,
        scalaCheck
      )
  )
  .dependsOn(
    `baas-node-client`,
    `baas-client-example`,
    `baas-interaction-example-make-payment`,
    `baas-interaction-example-reserve-items`,
    `baas-interaction-example-ship-items`)

lazy val `sbt-baas-docker-generate` = project.in(file("sbt-baas-docker-generate"))
  .settings(defaultModuleSettings)
  .settings(
    // workaround to let plugin be used in the same project without publishing it
    sourceGenerators in Compile += Def.task {
      val file = (sourceManaged in Compile).value / "baas" / "sbt" / "BuildInteractionDockerImageSBTPlugin.scala"
      val sourceFile = IO.readBytes(baseDirectory.value.getParentFile / "project" / "BuildInteractionDockerImageSBTPlugin.scala")
      IO.write(file, sourceFile)
      Seq(file)
    }.taskValue,
    addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.6.0"),
    addSbtPlugin("org.vaslabs.kube" % "sbt-kubeyml" % "0.3.1")
  )
  .enablePlugins(SbtPlugin)