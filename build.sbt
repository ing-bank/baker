import Dependencies._
import sbt.Keys._
import sbt.file

def testScope(project: ProjectReference): ClasspathDep[ProjectReference] = project % "test->test;test->compile"

lazy val buildExampleDockerCommand: Command = Command.command("buildExampleDocker")({
  state =>
    val extracted = Project.extract(state)

    "bakery-baker-docker-generate/docker:publishLocal" ::
      "bakery-client-example/docker:publishLocal" ::
      "bakery-kafka-listener-example/docker:publishLocal" ::
      "bakery-controller-docker-generate/docker:publishLocal" ::
      "project bakery-interaction-example-make-payment-and-ship-items" ::
      "buildInteractionDockerImage --image-name=interaction-make-payment-and-ship-items --publish=local --interaction=webshop.webservice.MakePaymentInstance --interaction=webshop.webservice.ShipItemsInstance" ::
      "project bakery-interaction-example-reserve-items" ::
      "buildInteractionDockerImage --image-name=bakery-interaction-example-reserve-items --publish=local --interaction=webshop.webservice.ReserveItemsConfiguration --springEnabled=true" ::
      "project bakery-integration-tests" ::
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
  coverageExcludedPackages := "<empty>;.*javadsl.*;.*scaladsl.*;.*common.*;.*protobuf.*;.*Main.*",
  packageOptions in(Compile, packageBin) +=
    Package.ManifestAttributes(
      "Build-Time" -> new java.util.Date().toString,
      "Build-Commit" -> git.gitHeadCommit.value.getOrElse("No Git Revision Found")
    ),
  resolvers += Resolver.bintrayRepo("cakesolutions", "maven"),
  maintainer in Docker := "The Bakery Team",
  dockerRepository in Docker := sys.env.get("BAKERY_DOCKER_REPO"),
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

lazy val `baker-types` = project.in(file("core/baker-types"))
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

lazy val `baker-intermediate-language` = project.in(file("core/intermediate-language"))
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
  ).dependsOn(`baker-types`)

lazy val `baker-interface` = project.in(file("core/baker-interface"))
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
  .dependsOn(`baker-intermediate-language`)

lazy val `baker-akka-runtime` = project.in(file("core/akka-runtime"))
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
        akkaClusterBoostrap,
        akkaDiscovery,
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
    `baker-intermediate-language`,
    `baker-interface`,
    testScope(`baker-recipe-dsl`),
    testScope(`baker-recipe-compiler`),
    testScope(`baker-types`))
  .enablePlugins(MultiJvmPlugin)
  .configs(MultiJvm)

lazy val `baker-recipe-dsl` = project.in(file("core/recipe-dsl"))
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
  ).dependsOn(`baker-types`)

lazy val `baker-recipe-compiler` = project.in(file("core/recipe-compiler"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-compiler",
    libraryDependencies ++=
      testDeps(scalaTest, scalaCheck, junitJupiter)
  )
  .dependsOn(`baker-recipe-dsl`, `baker-intermediate-language`, testScope(`baker-recipe-dsl`))


lazy val `bakery-interaction-protocol` = project.in(file("bakery/interaction-protocol"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "bakery-interaction-protocol",
    libraryDependencies ++= Seq(
      http4s,
      http4sDsl,
      http4sClient,
      http4sCirce
    )
  )
  .dependsOn(`baker-interface`)

lazy val `bakery-baker-client` = project.in(file("bakery/baker-client"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "bakery-baker-client",
    libraryDependencies ++= Seq(
      http4s,
      http4sDsl,
      http4sClient,
      http4sCirce,
      scalaLogging,
      http4sServer % "test",
      slf4jApi % "test",
      logback % "test",
      scalaTest % "test"
    )
  )
  .dependsOn(`baker-interface`)

lazy val `bakery-baker` = project.in(file("bakery/baker"))
  .settings(commonSettings ++ Publish.settings)
  .settings(
    moduleName := "bakery-baker",
    scalacOptions ++= Seq(
      "-Ypartial-unification"
    ),
    libraryDependencies ++= Seq(
      slf4jApi,
      akkaPersistenceCassandra,
      akkaManagementHttp,
      akkaClusterBoostrap,
      akkaDiscovery,
      akkaDiscoveryKube,
      skuber,
      play,
      jackson,
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
    ),
    dependencyOverrides ++= Seq(
      play
    )
  )
  .dependsOn(
    `baker-akka-runtime`,
    `bakery-baker-client`,
    `bakery-interaction-protocol`,
    `baker-recipe-compiler`, `baker-recipe-dsl`, `baker-intermediate-language`
  )

lazy val `bakery-interaction` = project.in(file("bakery/interaction"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "bakery-interaction",
    libraryDependencies ++= Seq(
      slf4jApi,
      http4s,
      http4sDsl,
      http4sServer,
      http4sCirce,
      circe,
      catsEffect,
      catsCore,
      kamon,
      kamonPrometheus
    ) ++ testDeps(
      scalaTest,
      logback
    )
  )
  .dependsOn(`bakery-interaction-protocol`, `baker-interface`)

lazy val `bakery-interaction-spring` = project.in(file("bakery/interaction-spring"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "bakery-interaction-spring",
    libraryDependencies ++= Seq(
      slf4jApi,
      http4s,
      http4sDsl,
      http4sServer,
      http4sCirce,
      circe,
      catsEffect,
      catsCore,
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
  .dependsOn(`bakery-interaction`, `baker-recipe-dsl`)

lazy val `bakery-controller` = project.in(file("bakery/controller"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "bakery-controller",
    libraryDependencies ++= Seq(
      slf4jApi,
      akkaSlf4j,
      scalaLogging,
      skuber,
      play,
      jackson,
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
    ),
    dependencyOverrides ++= Seq(
      play
    )
  )
  .dependsOn(`baker-types`, `baker-recipe-compiler`, `baker-recipe-dsl`, `baker-intermediate-language`, `bakery-baker-client`, `bakery-interaction-protocol`)

lazy val `bakery-controller-docker-generate` = project.in(file("docker/bakery-controller-docker-generate"))
  .settings(commonSettings, noPublishSettings)
  .enablePlugins(JavaAppPackaging, DockerPlugin)
  .settings(
    packageSummary in Docker := "The bakery controller",
    packageName in Docker := "bakery-controller",
    mainClass in Compile := Some("com.ing.bakery.clustercontroller.Main"),
    libraryDependencies ++= Seq(
      logback
    )
  )
  .dependsOn(`bakery-controller`)

lazy val `bakery-baker-docker-generate` = project.in(file("docker/bakery-baker-docker-generate"))
  .settings(commonSettings, noPublishSettings)
  .enablePlugins(JavaAppPackaging, DockerPlugin)
  .settings(
    packageSummary in Docker := "The bakery state node",
    packageName in Docker := "bakery-baker",
    mainClass in Compile := Some("com.ing.bakery.baker.Main"),
    libraryDependencies ++= Seq(
      logback
    )
  )
  .dependsOn(`bakery-baker`)

lazy val baker = project.in(file("."))
  .settings(defaultModuleSettings)
  .aggregate(`baker-types`, `baker-akka-runtime`, `baker-recipe-compiler`, `baker-recipe-dsl`, `baker-intermediate-language`,
    `bakery-baker-client`, `bakery-baker`, `bakery-interaction`, `bakery-interaction-spring`, `bakery-interaction-protocol`,
    `sbt-bakery-docker-generate`,
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
  .dependsOn(`baker-types`, `baker-akka-runtime`, `baker-recipe-compiler`, `baker-recipe-dsl`, `baker-intermediate-language`)

lazy val `bakery-client-example` = project
  .in(file("examples/bakery-client-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "bakery-client-example",
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
    packageSummary in Docker := "A web-shop checkout service example running on bakery",
    packageName in Docker := "bakery-client-example"
  )
  .dependsOn(`baker-types`, `bakery-baker-client`, `baker-recipe-compiler`, `baker-recipe-dsl`)

lazy val `bakery-kafka-listener-example` = project
  .in(file("examples/bakery-kafka-listener-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "bakery-kafka-listener-example",
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
    packageSummary in Docker := "A web-shop checkout service example running on bakery",
    packageName in Docker := "bakery-kafka-listener-example"
  )
  .dependsOn(`baker-types`, `bakery-baker-client`, `baker-recipe-compiler`, `baker-recipe-dsl`)

lazy val `bakery-interaction-example-reserve-items` = project.in(file("examples/bakery-interaction-examples/reserve-items"))
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(bakery.sbt.BuildInteractionDockerImageSBTPlugin)
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "bakery-interaction-example-reserve-items",
    scalacOptions ++= Seq(
      "-Ypartial-unification"
    ),
    libraryDependencies ++=
      compileDeps(
        logback,
        catsEffect,
        springCore,
        springContext
      ) ++ testDeps(
        scalaTest,
        scalaCheck
      )
  )
  .dependsOn(`bakery-interaction`, `baker-recipe-dsl`)

lazy val `bakery-interaction-example-make-payment-and-ship-items` = project.in(file("examples/bakery-interaction-examples/make-payment-and-ship-items"))
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(bakery.sbt.BuildInteractionDockerImageSBTPlugin)
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "bakery-interaction-example-make-payment-and-ship-items",
    scalacOptions ++= Seq(
      "-Ypartial-unification"
    ),
    libraryDependencies ++=
      compileDeps(
        logback,
        catsEffect
      ) ++ testDeps(
        scalaTest,
        scalaCheck,
        scalaCheckPlus
      )
  )
  .dependsOn(`bakery-interaction`)

lazy val `bakery-integration-tests` = project.in(file("bakery-integration-tests"))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)
  .settings(
    moduleName := "bakery-integration-tests",
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
    `bakery-baker-client`,
    `bakery-client-example`,
    `bakery-interaction-example-make-payment-and-ship-items`,
    `bakery-interaction-example-reserve-items`)

lazy val `sbt-bakery-docker-generate` = project.in(file("docker/sbt-bakery-docker-generate"))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings) // docker plugin can't be published, at least not to azure feed
  .settings(
    // workaround to let plugin be used in the same project without publishing it
    sourceGenerators in Compile += Def.task {
      val file = (sourceManaged in Compile).value / "bakery" / "sbt" / "BuildInteractionDockerImageSBTPlugin.scala"
      val sourceFile = IO.readBytes(baseDirectory.value.getParentFile.getParentFile / "project" / "BuildInteractionDockerImageSBTPlugin.scala")
      IO.write(file, sourceFile)
      Seq(file)
    }.taskValue,
    addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.6.0"),
    addSbtPlugin("org.vaslabs.kube" % "sbt-kubeyml" % "0.3.9")
  )
  .enablePlugins(SbtPlugin)
  .enablePlugins(bakery.sbt.BuildInteractionDockerImageSBTPlugin)
  .dependsOn(`bakery-interaction`, `bakery-interaction-spring`)
