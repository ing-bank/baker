import Dependencies._
import com.typesafe.sbt.packager.MappingsHelper.directory
import sbt.Keys._
import sbt.file

import scala.sys.process.Process

def testScope(project: ProjectReference): ClasspathDep[ProjectReference] = project % "test->test;test->compile"

lazy val buildExampleDockerCommand: Command = Command.command("buildExampleDocker")({
  state =>
    "set ThisBuild / version := \"local\"" ::
     "bakery-state/Docker/publishLocal" ::
      "bakery-client-example/Docker/publishLocal" ::
      "bakery-kafka-listener-example/Docker/publishLocal" ::
      "project interaction-example-make-payment-and-ship-items" ::
      "buildInteractionDockerImage --image-name=interaction-make-payment-and-ship-items --publish=local --interaction=webshop.webservice.MakePaymentInstance --interaction=webshop.webservice.ShipItemsInstance" ::
      "project interaction-example-reserve-items" ::
      "buildInteractionDockerImage --image-name=interaction-example-reserve-items --publish=local --interaction=webshop.webservice.ReserveItemsConfiguration --springEnabled=true" ::
      "project bakery-integration-tests" ::
      state
})

val commonSettings = Defaults.coreDefaultSettings ++ Seq(
  organization := "com.ing.baker",
  scalaVersion := "2.13.7",
  fork := true,
  testOptions += Tests.Argument(TestFrameworks.JUnit, "-v"),
  javacOptions := Seq("-source", "1.8", "-target", "1.8"),
  scalacOptions := Seq(
    s"-target:jvm-1.8",
    "-unchecked",
    "-deprecation",
    "-feature",
    "-language:higherKinds",
    "-language:existentials",
    "-language:implicitConversions",
    "-language:postfixOps",
    "-encoding", "utf8",
    "-Xfatal-warnings"
  ),
  coverageExcludedPackages := "<empty>;bakery.sbt;.*javadsl.*;.*scaladsl.*;.*common.*;.*protobuf.*;.*protomappings.*;.*Main.*",
  packageBin / packageOptions +=
    Package.ManifestAttributes(
      "Build-Time" -> new java.util.Date().toString,
      "Build-Commit" -> git.gitHeadCommit.value.getOrElse("No Git Revision Found")
    )
)

val dockerSettings = Seq(
  Docker / maintainer := "The Bakery Team",
  dockerBaseImage := "adoptopenjdk/openjdk11",
  dockerUpdateLatest := true, // todo only for master branch
  Docker / version := "local", // used by smoke tests for locally built images
)

val dependencyOverrideSettings = Seq(
  libraryDependencies ++= Seq(
    snakeYaml,
    jacksonDatabind,
    bouncyCastleBcprov,
    bouncyCastleBcpkix
  ),
  dependencyOverrides ++= Seq(
    catsCore,
    akkaActor,
    akkaStream,
    akkaProtobuf,
    jnrConstants,
    snakeYaml,
    jacksonDatabind,
    bouncyCastleBcprov,
    bouncyCastleBcpkix
  )
)

lazy val noPublishSettings = Seq(
  publish := {},
  publishLocal := {},
  publishArtifact := false
)

lazy val defaultModuleSettings = commonSettings ++ dependencyOverrideSettings ++ Publish.settings

lazy val scalaPBSettings = Seq(Compile / PB.targets := Seq(scalapb.gen() -> (Compile / sourceManaged).value))

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
      fs2Core,
      fs2Io,
      scalaJava8Compat,
      javaxInject,
      guava
    ) ++ providedDeps(findbugs) ++ testDeps(
      scalaTest,
      scalaCheckPlusMockito,
      mockito,
      slf4jApi,
      logback
    )
  )
  .dependsOn(
    `baker-intermediate-language`,
    `baker-annotations`,
    testScope(`baker-recipe-dsl`),
    testScope(`baker-recipe-compiler`),
    testScope(`baker-types`))

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
        akkaInmemoryJournal,
        akkaSlf4j,
        ficusConfig,
        catsCore,
        catsEffect,
        scalapbRuntime,
        protobufJava,
        slf4jApi,
        scalaLogging,
        sensors
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
        logback,
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

lazy val `baker-annotations` = project.in(file("core/baker-annotations"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-annotations",
    libraryDependencies ++= compileDeps(javaxInject)
  )

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
  ).dependsOn(`baker-types`, `baker-annotations`)

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
      http4sServer,
      http4sClient,
      http4sCirce,
      http4sPrometheus,
      prometheus,
      prometheusJmx
    )
  )
  .dependsOn(`baker-interface`)

lazy val `bakery-client` = project.in(file("bakery/client"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "bakery-client",
    libraryDependencies ++= Seq(
      http4s,
      http4sDsl,
      http4sClient,
      http4sCirce,
      scalaLogging,
      catsRetry,
      http4sServer % "test",
      slf4jApi % "test",
      logback % "test",
      scalaTest % "test",
      mockitoScala % "test",
      mockitoScalaTest % "test"
    )
  )
  .dependsOn(`baker-interface`)

val npmBuildTask = taskKey[File]("Dashboard build")

lazy val `bakery-dashboard` = project.in(file("bakery/dashboard"))
  .enablePlugins(UniversalPlugin)
  .settings(defaultModuleSettings)
  .settings(
    name := "bakery-dashboard",
    maintainer := "The Bakery Team",
    Universal / packageName  := s"bakery-dashboard",
    Universal / mappings ++= Seq(file("dashboard.zip") -> "dashboard.zip"),
    npmBuildTask := {
      val processBuilder = Process("./npm-build.sh", file("bakery/dashboard"))
      val process = processBuilder.run()
      if(process.exitValue() != 0) throw new Error(s"NPM failed with exit value ${process.exitValue()}")
      file("bakery/dashboard/dashboard.zip")
    },
    crossPaths := false,
    Compile / doc / sources  := Seq.empty,
    Compile / packageDoc / mappings := Seq(),
    Compile / packageDoc / publishArtifact := false,
    Compile / packageSrc / publishArtifact := false,
    Compile / packageBin / publishArtifact := false,
    Universal / packageBin  := npmBuildTask.value,
    addArtifact(Artifact("dashboard", "zip", "zip"), npmBuildTask),
    publish := (publish dependsOn (Universal / packageBin)).value,
    publishLocal := (publishLocal dependsOn (Universal / packageBin)).value
  )

lazy val `bakery-state` = project.in(file("bakery/state"))
  .enablePlugins(JavaAppPackaging, DockerPlugin)
  .settings(defaultModuleSettings)
  .settings(
    Compile / mainClass := Some("com.ing.bakery.baker.Main"),
    dockerExposedPorts ++= Seq(8080),
    Docker / packageName := "bakery-state",
    dockerBaseImage := "adoptopenjdk/openjdk11",
    Universal / mappings ++=
      directory(s"${(`bakery-dashboard` / baseDirectory).value.getAbsolutePath}/dist")
        .map(t => (t._1, t._2.replace("dist", "dashboard"))),
    moduleName := "bakery-state",
    scalacOptions ++= Seq(
      "-Ypartial-unification"
    ),
    libraryDependencies ++= Seq(
      slf4jApi,
      logback,
      akkaPersistenceCassandra,
      akkaHttpSprayJson,
      akkaManagementHttp,
      akkaClusterBoostrap,
      akkaClusterMetrics,
      akkaDiscovery,
      akkaDiscoveryKube,
      http4s,
      http4sDsl,
      http4sCirce,
      http4sServer,
      kafkaClient,
      skuber
    ) ++ testDeps(
      slf4jApi,
      logback,
      scalaTest,
      mockServer,
      circe,
      circeGeneric,
      akkaInmemoryJournal,
      cassandraDriverCore,
      cassandraDriverQueryBuilder,
      cassandraDriverMetrics,
      cassandraUnit
    )
  )
  .dependsOn(
    `baker-akka-runtime`,
    `bakery-client`,
    `baker-interface`,
    `bakery-interaction-protocol`,
    `baker-recipe-compiler`,
    `baker-recipe-dsl`,
    `baker-intermediate-language`,
    `bakery-dashboard`
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
      springCore,
      springContext,
      scalaLogging
    ) ++ testDeps(
      scalaTest,
      logback
    )
  )
  .dependsOn(`bakery-interaction`, `baker-recipe-dsl`)

lazy val baker = project.in(file("."))
  .settings(defaultModuleSettings)
  .aggregate(`baker-types`, `baker-akka-runtime`, `baker-recipe-compiler`, `baker-recipe-dsl`, `baker-intermediate-language`,
    `bakery-client`, `bakery-state`, `bakery-interaction`, `bakery-interaction-spring`, `bakery-interaction-protocol`,
    `sbt-bakery-docker-generate`,
    `baker-interface`, `bakery-dashboard`, `baker-annotations`)

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
  .settings(dockerSettings)
  .settings(
    Docker / packageName := "baker-example-app",
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
  .settings(dockerSettings)
  .settings(
    Docker / packageName := "bakery-client-example"
  )
  .dependsOn(`baker-types`, `bakery-client`, `baker-recipe-compiler`, `baker-recipe-dsl`)

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
  .settings(dockerSettings)
  .settings(
    Docker / packageName := "bakery-kafka-listener-example"
  )
  .dependsOn(`baker-types`, `bakery-client`, `baker-recipe-compiler`, `baker-recipe-dsl`)

lazy val `interaction-example-reserve-items` = project.in(file("examples/bakery-interaction-examples/reserve-items"))
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(bakery.sbt.BuildInteractionDockerImageSBTPlugin)
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "interaction-example-reserve-items",
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

lazy val `interaction-example-make-payment-and-ship-items` = project.in(file("examples/bakery-interaction-examples/make-payment-and-ship-items"))
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(bakery.sbt.BuildInteractionDockerImageSBTPlugin)
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "interaction-example-make-payment-and-ship-items",
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

lazy val `bakery-integration-tests` = project.in(file("bakery/integration-tests"))
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
    `bakery-client`,
    `bakery-client-example`,
    `interaction-example-make-payment-and-ship-items`,
    `interaction-example-reserve-items`)

lazy val `sbt-bakery-docker-generate` = project.in(file("docker/sbt-bakery-docker-generate"))
  .settings(defaultModuleSettings)
  .settings(noPublishSettings) // docker plugin can't be published, at least not to azure feed
  .settings(
    // workaround to let plugin be used in the same project without publishing it
    Compile / sourceGenerators  += Def.task {
      val file = (Compile / sourceManaged).value / "bakery" / "sbt" / "BuildInteractionDockerImageSBTPlugin.scala"
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

lazy val `baker-test` = project.in(file("core/baker-test"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baker-test",
    libraryDependencies ++= compileDeps(
      slf4jApi
    ) ++ testDeps(scalaTest, logback,
      "io.altoo" %% "akka-kryo-serialization" % "1.1.5",
      "junit" % "junit" % "4.13",
      "org.scalatestplus" %% "junit-4-13" % "3.2.9.0"
    )
  ).dependsOn(`baker-interface`, testScope(`baker-akka-runtime`), testScope(`baker-recipe-compiler`))

