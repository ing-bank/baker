import Dependencies._
import sbt.Keys._

def testScope(project: ProjectReference): ClasspathDep[ProjectReference] = project % "test->test;test->compile"

lazy val buildExampleDockerCommand: Command = Command.command("buildExampleDocker")({
  state =>
    val extracted = Project.extract(state)

    "baas-node-state/docker:publishLocal" ::
      "baas-client-example/docker:publishLocal" ::
      "baas-kafka-listener-example/docker:publishLocal" ::
      "bakery-controller/docker:publishLocal" ::
      "project baas-interaction-example-make-payment-and-ship-items" ::
      "buildInteractionDockerImage --image-name=interaction-make-payment-and-ship-items --publish=local --interaction=webshop.webservice.MakePaymentInstance --interaction=webshop.webservice.ShipItemsInstance" ::
      "project baas-interaction-example-reserve-items" ::
      "buildInteractionDockerImage --image-name=baas-interaction-example-reserve-items --publish=local --interaction=webshop.webservice.ReserveItemsInstance" ::
      "project baas-smoke-tests" ::
      state
})

val commonSettings = Defaults.coreDefaultSettings ++ Seq(
  organization := "com.ing.baker",
  scalaVersion := "2.12.11",
  crossScalaVersions := Seq("2.12.11"),
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
    ),
  resolvers += Resolver.bintrayRepo("cakesolutions", "maven"),
  maintainer in Docker := "The Bakery Team",
  dockerRepository in Docker := sys.env.get("BAAS_DOCKER_REPO"),
  version in Docker := "local" // used by smoke tests for locally built images
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

lazy val defaultModuleSettings = commonSettings ++ dependencyOverrideSettings ++ Publish.settings

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
    ) ++ testDeps(scalaTest, scalaCheck, scalaCheckPlus)
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
    ) ++ testDeps(scalaTest, scalaCheck, scalaCheckPlus)
  ).dependsOn(bakertypes)

lazy val `baker-interface` = project.in(file("baker-interface"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baker-interface",
    libraryDependencies ++= Seq(
      circe,
      circeParser,
      circeGeneric,
      circeGenericExtras,
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
    libraryDependencies ++=
      compileDeps(
        akkaActor,
        akkaPersistence,
        akkaPersistenceQuery,
        akkaCluster,
        akkaClusterTools,
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
        scalaCheckPlus,
        scalaCheckPlusMockito,
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
    libraryDependencies ++=
      compileDeps(
        javaxInject,
        paranamer,
        scalaReflect(scalaVersion.value),
      ) ++
        testDeps(
          scalaTest,
          scalaCheck,
          scalaCheckPlus,
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


lazy val `bakery-interaction-api` = project.in(file("bakery-interaction-api"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "bakery-interaction-api",
    libraryDependencies ++= Seq(
      http4s,
      http4sDsl,
      http4sClient,
      http4sCirce
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
      http4sClient,
      http4sCirce
    )
  )
  .dependsOn(`baker-interface`)

lazy val `baas-node-state` = project.in(file("baas-node-state"))
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(DockerPlugin)
  .settings(commonSettings ++ Publish.settings)
  .settings(
    moduleName := "baas-node-state",
    scalacOptions ++= Seq(
      "-Ypartial-unification"
    ),
    libraryDependencies ++= Seq(
      slf4jApi,
      logback,
      akkaPersistenceCassandra,
      akkaManagementHttp,
      akkaClusterBoostrap,
      akkaDiscoveryKube,
      skuber,
      http4s,
      http4sDsl,
      http4sCirce,
      http4sServer,
      scalaKafkaClient,
      kamon,
      kamonAkka,
      kamonPrometheus
    ) ++ testDeps(
      slf4jApi,
      logback,
      scalaTest,
      mockServer,
      circe,
      circeGeneric
    )
  )
  .settings(
    packageSummary in Docker := "The core node",
    packageName in Docker := "baas-node-state"
  )
  .dependsOn(
    runtime,
    `baas-node-client`,
    `bakery-interaction-api`,
    recipeCompiler, recipeDsl, intermediateLanguage
  )

lazy val `bakery-interaction` = project.in(file("bakery-interaction"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "bakery-interaction",
    libraryDependencies ++= Seq(
      slf4jApi,
      logback,
      http4s,
      http4sDsl,
      http4sServer,
      catsEffect,
      catsCore,
      kamon,
      kamonPrometheus
    ) ++ testDeps(
      scalaTest,
      logback
    )
  )
  .dependsOn(`bakery-interaction-api`, `baker-interface`)

lazy val `bakery-interaction-spring` = project.in(file("bakery-interaction-spring"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "bakery-interaction-spring",
    libraryDependencies ++= Seq(
      slf4jApi,
      logback,
      http4s,
      http4sDsl,
      http4sServer,
      kamon,
      kamonPrometheus,
      springCore,
      springContext,
      scalaLogging
    ) ++ testDeps(
      scalaTest,
      logback
    )
  )
  .dependsOn(`bakery-interaction`, `recipeDsl`)

lazy val `bakery-controller` = project.in(file("bakery-controller"))
  .settings(defaultModuleSettings)
  .enablePlugins(JavaAppPackaging, JavaAgent)
  .settings(
    packageSummary in Docker := "The bakery controller",
    packageName in Docker := "bakery-controller"
  )
  .settings(
    moduleName := "bakery-controller",
    javaAgents += "io.kamon" % "kanela-agent" % "1.0.5",
    libraryDependencies ++= Seq(
      slf4jApi,
      akkaSlf4j,
      logback,
      scalaLogging,
      skuber,
      http4s,
      http4sDsl,
      http4sServer,
      kamon,
      kamonPrometheus
    ) ++ testDeps(
      slf4jApi,
      logback,
      scalaTest,
      mockServer,
      circe,
      circeGeneric
    )
  )
  .dependsOn(bakertypes, recipeCompiler, recipeDsl, intermediateLanguage, `baas-node-client`, `bakery-interaction-api`)

lazy val baker = project.in(file("."))
  .settings(defaultModuleSettings)
  .aggregate(bakertypes, runtime, recipeCompiler, recipeDsl, intermediateLanguage, splitBrainResolver,
    `baas-node-client`, `baas-node-state`, `bakery-interaction`, `bakery-interaction-api`,
    `sbt-baas-docker-generate`,
    `baker-interface`, `bakery-controller`)

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
    packageSummary in Docker := "A web-shop checkout service example running baker",
    packageName in Docker := "baker-example-app",
    dockerExposedPorts := Seq(8080)
  )
  .dependsOn(bakertypes, runtime, recipeCompiler, recipeDsl, intermediateLanguage)

lazy val `baas-client-example` = project
  .in(file("examples/baas-client-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baas-client-example",
    scalacOptions ++= Seq(
      "-Ypartial-unification"
    ),
    libraryDependencies ++=
      compileDeps(
        slf4jApi,
        logback,
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
    packageSummary in Docker := "A web-shop checkout service example running on baas",
    packageName in Docker := "baas-client-example"
  )
  .dependsOn(bakertypes, `baas-node-client`, recipeCompiler, recipeDsl)

lazy val `baas-kafka-listener-example` = project
  .in(file("examples/baas-kafka-listener-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baas-kafka-listener-example",
    scalacOptions ++= Seq(
      "-Ypartial-unification"
    ),
    libraryDependencies ++=
      compileDeps(
        slf4jApi,
        circe,
        circeGeneric,
        circeGenericExtras,
        fs2kafka,
        ficusConfig
      ) ++ testDeps(
        scalaTest,
        scalaCheck
      )
  )
  .settings(
    packageSummary in Docker := "A web-shop checkout service example running on baas",
    packageName in Docker := "baas-kafka-listener-example"
  )
  .dependsOn(bakertypes, `baas-node-client`, recipeCompiler, recipeDsl)

lazy val `baas-interaction-example-reserve-items` = project.in(file("examples/baas-interaction-examples/reserve-items"))
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(baas.sbt.BuildInteractionDockerImageSBTPlugin)
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baas-interaction-example-reserve-items",
    scalacOptions ++= Seq(
      "-Ypartial-unification"
    ),
    libraryDependencies ++=
      compileDeps(
        slf4jApi,
        catsEffect
      ) ++ testDeps(
        scalaTest,
        scalaCheck
      )
  )
  .dependsOn(`bakery-interaction`)

lazy val `baas-interaction-example-make-payment-and-ship-items` = project.in(file("examples/baas-interaction-examples/make-payment-and-ship-items"))
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(baas.sbt.BuildInteractionDockerImageSBTPlugin)
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baas-interaction-example-make-payment-and-ship-items",
    scalacOptions ++= Seq(
      "-Ypartial-unification"
    ),
    libraryDependencies ++=
      compileDeps(
        slf4jApi,
        catsEffect
      ) ++ testDeps(
        scalaTest,
        scalaCheck,
        scalaCheckPlus
      )
  )
  .dependsOn(`bakery-interaction`)

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
        scalaTest,
        scalaCheck
      )
  )
  .dependsOn(
    `baas-node-client`,
    `baas-client-example`,
    `baas-interaction-example-make-payment-and-ship-items`,
    `baas-interaction-example-reserve-items`)

lazy val `sbt-baas-docker-generate` = project.in(file("sbt-baas-docker-generate"))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings) // docker plugin can't be published, at least not to azure feed
  .settings(
    // workaround to let plugin be used in the same project without publishing it
    sourceGenerators in Compile += Def.task {
      val file = (sourceManaged in Compile).value / "baas" / "sbt" / "BuildInteractionDockerImageSBTPlugin.scala"
      val sourceFile = IO.readBytes(baseDirectory.value.getParentFile / "project" / "BuildInteractionDockerImageSBTPlugin.scala")
      IO.write(file, sourceFile)
      Seq(file)
    }.taskValue,
    addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.6.0"),
    addSbtPlugin("org.vaslabs.kube" % "sbt-kubeyml" % "0.3.4")
  )
  .enablePlugins(SbtPlugin)
  .enablePlugins(baas.sbt.BuildInteractionDockerImageSBTPlugin)
  .dependsOn(`bakery-interaction`)
