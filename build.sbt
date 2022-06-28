import Dependencies._
import com.typesafe.sbt.packager.MappingsHelper.directory
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

lazy val scala212 = "2.12.16"
lazy val scala213 = "2.13.8"

lazy val supportedScalaVersions = List(scala213, scala212)
val commonSettings: Seq[Setting[_]] = Defaults.coreDefaultSettings ++ Seq(
  organization := "com.ing.baker",
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

val dockerSettings: Seq[Setting[_]] = Seq(
  Docker / maintainer := "The Bakery Team",
  dockerBaseImage := "adoptopenjdk/openjdk11",
  dockerUpdateLatest := true, // todo only for master branch
  Docker / version := "local", // used by smoke tests for locally built images
)

val dependencyOverrideSettings: Seq[Setting[_]] = Seq(
  libraryDependencies ++= Seq(
    snakeYaml,
    jacksonDatabind,
    jacksonCore,
    jawnParser,
    nettyHandler,
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
    jacksonCore,
    jawnParser,
    nettyHandler,
    bouncyCastleBcprov,
    bouncyCastleBcpkix,
  )
)

lazy val noPublishSettings: Seq[Setting[_]] = Seq(
  publish := {},
  publishLocal := {},
  publishArtifact := false
)

lazy val crossBuildSettings: Seq[Setting[_]] = Seq(
  scalaVersion := scala213,
  crossScalaVersions := supportedScalaVersions
)

lazy val defaultModuleSettings212: Seq[Setting[_]] = commonSettings ++ dependencyOverrideSettings ++ Publish.settings

lazy val defaultModuleSettings: Seq[Setting[_]] =  crossBuildSettings ++ defaultModuleSettings212

lazy val yPartialUnificationSetting: Seq[Setting[_]] = Seq(
  Compile / scalacOptions ++= {
    CrossVersion.partialVersion(scalaVersion.value) match {
      case Some((2, n)) if n <= 12 => List("-Ypartial-unification")
      case _ => Nil
    }
  }
)

lazy val scalaPBSettings: Seq[Setting[_]] = Seq(Compile / PB.targets := Seq(scalapb.gen() -> (Compile / sourceManaged).value))

lazy val `baker-types`: Project = project.in(file("core/baker-types"))
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

lazy val `baker-intermediate-language`: Project = project.in(file("core/intermediate-language"))
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

lazy val `baker-interface`: Project = project.in(file("core/baker-interface"))
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
      CrossVersion.partialVersion(scalaVersion.value) match {
        case Some((2, n)) if n <= 12 =>
          scalaJava8Compat091
        case _ =>
          scalaJava8Compat100
      },
      javaxInject,
      guava
    ) ++ providedDeps(findbugs) ++ testDeps(
      scalaTest,
      scalaCheckPlusMockito,
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

lazy val `baker-akka-runtime`: Project = project.in(file("core/akka-runtime"))
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
        akkaActorTyped,
        akkaClusterTyped,
        akkaPersistenceTyped,
        akkaStreamTyped,
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
        scalaCheckPlusMockito)
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

lazy val `baker-annotations`: Project = project.in(file("core/baker-annotations"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-annotations",
    libraryDependencies ++= compileDeps(javaxInject)
  )

lazy val `baker-recipe-dsl`: Project = project.in(file("core/recipe-dsl"))
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

lazy val `baker-recipe-compiler`: Project = project.in(file("core/recipe-compiler"))
  .settings(defaultModuleSettings)
  .settings(
    moduleName := "baker-compiler",
    libraryDependencies ++=
      testDeps(scalaTest, scalaCheck, junitJupiter)
  )
  .dependsOn(`baker-recipe-dsl`, `baker-intermediate-language`, testScope(`baker-recipe-dsl`))


lazy val `bakery-interaction-protocol`: Project = project.in(file("bakery/interaction-protocol"))
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

lazy val `bakery-client`: Project = project.in(file("bakery/client"))
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

lazy val `bakery-dashboard`: Project = project.in(file("bakery/dashboard"))
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
    Compile / doc / sources  := Seq.empty,
    Compile / packageDoc / mappings := Seq(),
    Compile / packageDoc / publishArtifact := false,
    Compile / packageSrc / publishArtifact := false,
    Compile / packageBin / publishArtifact := false,
    Universal / packageBin := npmBuildTask.value,
    addArtifact(Artifact("dashboard", "zip", "zip"), npmBuildTask),
    publish := (publish dependsOn (Universal / packageBin)).value,
    publishLocal := (publishLocal dependsOn (Universal / packageBin)).value
  )

lazy val `bakery-state-k8s`: Project = project.in(file("bakery/baker-state-k8s"))
  .settings(defaultModuleSettings)
  .settings(yPartialUnificationSetting)
  .settings(
    moduleName := "bakery-state-k8s",
    libraryDependencies ++= Seq(
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
    `bakery-dashboard`,
    `bakery-state` % "compile->compile;test->test"
  )


lazy val `bakery-state`: Project = project.in(file("bakery/state"))
  .enablePlugins(JavaAppPackaging, DockerPlugin)
  .settings(defaultModuleSettings)
  .settings(yPartialUnificationSetting)
  .settings(
    Compile / mainClass := Some("com.ing.bakery.baker.Main"),
    dockerExposedPorts ++= Seq(8080),
    Docker / packageName := "bakery-state",
    dockerBaseImage := "adoptopenjdk/openjdk11",
    Universal / mappings ++=
      directory(s"${(`bakery-dashboard` / baseDirectory).value.getAbsolutePath}/dist")
        .map(t => (t._1, t._2.replace("dist", "dashboard"))),
    moduleName := "bakery-state",
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
      akkaPki,
      http4s,
      http4sDsl,
      http4sCirce,
      http4sServer,
      kafkaClient
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

lazy val `bakery-interaction`: Project = project.in(file("bakery/interaction"))
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

lazy val `bakery-interaction-spring`: Project = project.in(file("bakery/interaction-spring"))
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

lazy val baker: Project = project.in(file("."))
  .settings(defaultModuleSettings)
  .settings(
    crossScalaVersions := Nil,
  )
  .aggregate(`baker-types`, `baker-akka-runtime`, `baker-recipe-compiler`, `baker-recipe-dsl`, `baker-intermediate-language`,
    `bakery-client`, `bakery-state`, `bakery-interaction`, `bakery-interaction-spring`, `bakery-interaction-protocol`,
    `bakery-state-k8s`, `baker-interface`, `bakery-dashboard`, `baker-annotations`, `baker-test`)

lazy val `baker-example`: Project = project
  .in(file("examples/baker-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(commonSettings)
  .settings(noPublishSettings)
  .settings(yPartialUnificationSetting)
  .settings(
    moduleName := "baker-example",
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
        mockitoScala,
        junitInterface,
        slf4jApi
      )
  )
  .settings(dockerSettings)
  .settings(
    Docker / packageName := "baker-example-app",
    dockerExposedPorts := Seq(8080)
  )
  .dependsOn(`baker-types`, `baker-akka-runtime`, `baker-recipe-compiler`, `baker-recipe-dsl`, `baker-intermediate-language`)

lazy val `bakery-client-example`: Project = project
  .in(file("examples/bakery-client-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(defaultModuleSettings)
  .settings(yPartialUnificationSetting)
  .settings(
    moduleName := "bakery-client-example",
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

lazy val `bakery-kafka-listener-example`: Project = project
  .in(file("examples/bakery-kafka-listener-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(defaultModuleSettings)
  .settings(yPartialUnificationSetting)
  .settings(
    moduleName := "bakery-kafka-listener-example",
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

lazy val `interaction-example-reserve-items`: Project = project.in(file("examples/bakery-interaction-examples/reserve-items"))
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(bakery.sbt.BuildInteractionDockerImageSBTPlugin)
  .settings(defaultModuleSettings)
  .settings(yPartialUnificationSetting)
  .settings(
    moduleName := "interaction-example-reserve-items",
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

lazy val `interaction-example-make-payment-and-ship-items`: Project = project.in(file("examples/bakery-interaction-examples/make-payment-and-ship-items"))
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(bakery.sbt.BuildInteractionDockerImageSBTPlugin)
  .settings(defaultModuleSettings)
  .settings(yPartialUnificationSetting)
  .settings(
    moduleName := "interaction-example-make-payment-and-ship-items",
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

lazy val `bakery-integration-tests`: Project = project.in(file("bakery/integration-tests"))
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

lazy val `sbt-bakery-docker-generate`: Project = project.in(file("docker/sbt-bakery-docker-generate"))
  .settings(scalaVersion := scala212, crossScalaVersions := Nil)
  .settings(defaultModuleSettings212)
  .settings(noPublishSettings) // docker plugin can't be published, at least not to azure feed
  .settings(
    crossScalaVersions := Nil,
    // workaround to let plugin be used in the same project without publishing it
    Compile / sourceGenerators += Def.task {
      val file = (Compile / sourceManaged).value / "bakery" / "sbt" / "BuildInteractionDockerImageSBTPlugin.scala"
      val sourceFile = IO.readBytes(baseDirectory.value.getParentFile.getParentFile / "project" / "BuildInteractionDockerImageSBTPlugin.scala")
      IO.write(file, sourceFile)
      Seq(file)
    }.taskValue,
    addSbtPlugin(("com.github.sbt" % "sbt-native-packager" % "1.9.9") cross CrossVersion.constant(scala212)),
    addSbtPlugin(("org.vaslabs.kube" % "sbt-kubeyml" % "0.4.0") cross CrossVersion.constant(scala212))
  )
  .enablePlugins(SbtPlugin)
  .enablePlugins(bakery.sbt.BuildInteractionDockerImageSBTPlugin)
  .dependsOn(`bakery-interaction`, `bakery-interaction-spring`)

lazy val `baker-test`: Project = project.in(file("core/baker-test"))
  .settings(defaultModuleSettings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baker-test",
    libraryDependencies ++= compileDeps(
      slf4jApi
    ) ++ testDeps(scalaTest, logback,
      "io.altoo" %% "akka-kryo-serialization" % "2.3.0",
      "junit" % "junit" % "4.13.2",
      "org.scalatestplus" %% "junit-4-13" % "3.2.11.0"
    )
  ).dependsOn(`baker-interface`, testScope(`baker-akka-runtime`), testScope(`baker-recipe-compiler`))

