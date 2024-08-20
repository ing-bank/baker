import Dependencies._
import sbt.file

import scala.sys.process.Process

lazy val baker: Project = project.in(file("."))
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
  .settings(
    crossScalaVersions := Nil
  )
  .aggregate(
    // Core
    `baker-types`, `baker-akka-runtime`, `baker-recipe-compiler`, `baker-recipe-dsl`, `baker-recipe-dsl-kotlin`, `baker-intermediate-language`,
    `baker-interface`, `baker-interface-kotlin`, `baker-annotations`, `baker-test`,
    // Http
    `baker-http-client`, `baker-http-server`, `baker-http-dashboard`,
    // Bakery
    `bakery-state`, `bakery-interaction`, `bakery-interaction-spring`, `bakery-interaction-protocol`,
    `bakery-interaction-k8s-interaction-manager`,
    // Examples
    `baker-example`, `bakery-client-example`, `interaction-example-make-payment-and-ship-items`,
    `interaction-example-reserve-items`, `bakery-kafka-listener-example`, `docs-code-snippets`
  )

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

lazy val scala213 = "2.13.14"

lazy val supportedScalaVersions = List(scala213)
val commonSettings: Seq[Setting[_]] = Defaults.coreDefaultSettings ++ Seq(
  organization := "com.ing.baker",
  fork := true,
  testOptions += Tests.Argument(TestFrameworks.JUnit, "-v"),
  javacOptions := Seq("-source", "17", "-target", "17"),
  scalacOptions := Seq(
    s"-target:jvm-17",
    "-unchecked",
    "-deprecation",
    "-feature",
    "-language:higherKinds",
    "-language:existentials",
    "-language:implicitConversions",
    "-language:postfixOps",
    "-encoding", "utf8",
//    "-Xfatal-warnings" //Cannot be enabled since we have deprecated our own methods and use them for now. Can be enabled again after we completely remove the depcrecated methods.
  ),
  coverageExcludedPackages := "<empty>;bakery.sbt;.*javadsl.*;.*scaladsl.*;.*common.*;.*protobuf.*;.*protomappings.*;.*Main.*",
  packageBin / packageOptions +=
    Package.ManifestAttributes(
      "Build-Time" -> new java.util.Date().toString,
      "Build-Commit" -> git.gitHeadCommit.value.getOrElse("No Git Revision Found")
    ),
  versionScheme := Some("semver-spec")
)

val dockerSettings: Seq[Setting[_]] = Seq(
  Docker / maintainer := "The Bakery Team",
  dockerBaseImage := "adoptopenjdk/openjdk11",
  dockerUpdateLatest := true, // todo only for master branch
  Docker / version := "local" // used by smoke tests for locally built images
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
    bouncyCastleBcpkix
  ),
  excludeDependencies ++= Seq(
    ExclusionRule("org.jetbrains.kotlin", "kotlin-scripting-compiler-embeddable")
  )
)

lazy val noPublishSettings: Seq[Setting[_]] = Seq(
  publish := {},
  publishArtifact := false,
  publishTo := Some(Resolver.file("Unused transient repository", file("target/unusedrepo")))
)

lazy val crossBuildSettings: Seq[Setting[_]] = Seq(
  scalaVersion := scala213,
  crossScalaVersions := supportedScalaVersions
)

lazy val defaultModuleSettings212: Seq[Setting[_]] = commonSettings ++ dependencyOverrideSettings

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
  .settings(Publish.settings)
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
  .settings(Publish.settings)
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
  .settings(Publish.settings)
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
      scalaJava8Compat100,
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

lazy val `baker-interface-kotlin`: Project = project.in(file("core/baker-interface-kotlin"))
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
  .settings(
    moduleName := "baker-interface-kotlin",
    kotlinVersion := "1.8.21",
    kotlincJvmTarget := "17",
    kotlinLib("stdlib-jdk8"),
    kotlinLib("reflect"),
    libraryDependencies ++=
      compileDeps(
        javaxInject,
        paranamer,
        scalaCollectionCompat,
        kotlinXCoroutinesCore,
        kotlinXCoroutinesJdk8,
        scalaReflect(scalaVersion.value)
      ) ++
        testDeps(
          scalaTest,
          scalaCheck,
          scalaCheckPlus,
          junitInterface,
          slf4jApi
        )
  ).dependsOn(`baker-interface`)

lazy val `baker-akka-runtime`: Project = project.in(file("core/akka-runtime"))
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
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
  .settings(Publish.settings)
  .settings(
    moduleName := "baker-annotations",
    libraryDependencies ++= compileDeps(javaxInject)
  )

lazy val `baker-recipe-dsl`: Project = project.in(file("core/recipe-dsl"))
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
  .settings(
    moduleName := "baker-recipe-dsl",
    libraryDependencies ++=
      compileDeps(
        javaxInject,
        paranamer,
        scalaCollectionCompat,
        scalaReflect(scalaVersion.value)
      ) ++
        testDeps(
          scalaTest,
          scalaCheck,
          scalaCheckPlus,
          junitInterface,
          slf4jApi
        )
  ).dependsOn(`baker-types`, `baker-annotations`)

lazy val `baker-recipe-dsl-kotlin`: Project = project.in(file("core/recipe-dsl-kotlin"))
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
  .settings(
    moduleName := "baker-recipe-dsl-kotlin",
    kotlinVersion := "1.8.21",
    kotlincJvmTarget := "17",
    kotlinLib("stdlib-jdk8"),
    kotlinLib("reflect"),
    libraryDependencies ++=
      compileDeps(
        javaxInject,
        paranamer,
        scalaCollectionCompat,
        scalaReflect(scalaVersion.value)
      ) ++
        testDeps(
          scalaTest,
          scalaCheck,
          scalaCheckPlus,
          junitInterface,
          slf4jApi
        )
  ).dependsOn(`baker-types`, `baker-annotations`, `baker-recipe-dsl`)

lazy val `baker-recipe-compiler`: Project = project.in(file("core/recipe-compiler"))
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
  .settings(
    moduleName := "baker-compiler",
    kotlinVersion := "1.8.21",
    kotlincJvmTarget := "17",
    libraryDependencies ++=
      testDeps(scalaTest, scalaCheck, junitJupiter)
  )
  .dependsOn(`baker-recipe-dsl`, `baker-recipe-dsl-kotlin`, `baker-intermediate-language`, testScope(`baker-recipe-dsl`), testScope(`baker-recipe-dsl-kotlin`))

lazy val `baker-test`: Project = project.in(file("core/baker-test"))
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
  .settings(scalaPBSettings)
  .settings(
    moduleName := "baker-test",
    libraryDependencies ++= compileDeps(
      slf4jApi
    ) ++ testDeps(scalaTest, logback,
      "io.altoo" %% "akka-kryo-serialization" % "2.4.3",
      "junit" % "junit" % "4.13.2",
      "org.scalatestplus" %% "junit-4-13" % "3.2.12.0"
    )
  ).dependsOn(`baker-interface`, testScope(`baker-akka-runtime`), testScope(`baker-recipe-compiler`))


lazy val `baker-http-client`: Project = project.in(file("http/baker-http-client"))
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
  .settings(
    moduleName := "baker-http-client",
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


lazy val `baker-http-server`: Project = project.in(file("http/baker-http-server"))
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
  .settings(yPartialUnificationSetting)
  .settings(
    moduleName := "baker-http-server",
    libraryDependencies ++= Seq(
      slf4jApi,
      logback,
      http4s,
      http4sDsl,
      http4sCirce,
      http4sServer,
      http4sPrometheus,
      prometheus,
      prometheusJmx
    ) ++ testDeps(mockitoScala, mockitoScalaTest, catsEffectTesting)
  )
  .dependsOn(
    `baker-interface`,
    `baker-http-dashboard`,
    testScope(`baker-recipe-compiler`)
  )

val npmInputFiles = taskKey[Set[File]]("List of files which are used by the npmBuildTask. Used to determine if something has changed and an npm build needs to be redone.")
val npmBuildTask = taskKey[File]("Uses NPM to build the dashboard into the dist directory")
val zipDistDirectory = taskKey[File]("Creates a zip file of the dashboard files")
val staticDashboardFilePrefix = settingKey[String]("Prefix for static files of dashboard in jar.")
val distDirectory = settingKey[File]("dist directory. This is like /target but for npm builds.")
val dashboardZipArtifact = settingKey[Artifact]("Creates the artifact object")
val dashboardFilesList = taskKey[Seq[File]]("List of static dashboard files")
val dashboardFilesIndex = taskKey[File]("Creates an index of dashboard resources.")
val prefixedDashboardResources = taskKey[Seq[File]]("Create resources containing dashboard files, prefixed.")

lazy val `baker-http-dashboard`: Project = project.in(file("http/baker-http-dashboard"))
  .enablePlugins(UniversalPlugin)
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
  .settings(
    name := "baker-http-dashboard",
    maintainer := "The Bakery Team",
    libraryDependencies ++= Seq(typeSafeConfig) ++ testDeps(
      scalaTest,
      logback
    ),
    Universal / packageName  := name.value,
    Universal / mappings += file("dashboard.zip") -> "dashboard.zip",
    staticDashboardFilePrefix := "dashboard_static",
    distDirectory := baseDirectory.value / "dist",
    npmInputFiles := {
      val sources = baseDirectory.value / "src" ** "*"
      val projectConfiguration = baseDirectory.value * "*.json"
      (sources.get() ++ projectConfiguration.get()).toSet
    },
    npmBuildTask := {
      // Caches the npm ./npm-build.sh execution. Invalidation is done if either
      // - anything is different in the baseDirectory / src, or files in the baseDirectory / *.json (compared using hash of file contents)
      // - dist directory doesn't contain the same files as previously.
      val cachedFunction = FileFunction.cached(streams.value.cacheDirectory / "npmBuild", inStyle = FileInfo.hash) { (in: Set[File]) =>
        val processBuilder = Process("./npm-build.sh", baseDirectory.value)
        val process = processBuilder.run()
        if (process.exitValue() != 0) throw new Error(s"NPM failed with exit value ${process.exitValue()}")
        val outputFiles = (distDirectory.value ** "*").get().toSet
        outputFiles
      }
      cachedFunction(npmInputFiles.value)
      distDirectory.value
    },
    zipDistDirectory := {
      val inputDirectory = npmBuildTask.value
      val targetZipFile = target.value / "dashboard.zip"
      IO.zip(
        sources = (inputDirectory ** "*").get().map(f => (f, inputDirectory.relativize(f).get.toString)),
        outputZip = targetZipFile)
      targetZipFile
    },
    prefixedDashboardResources := {
      val outputFolder = (Compile / resourceManaged).value / staticDashboardFilePrefix.value
      IO.copyDirectory(npmBuildTask.value, outputFolder)
      (outputFolder ** "*").get()
    },
    dashboardFilesList := {
      val distDir = npmBuildTask.value
      (distDir ** "*")
        .filter(_.isFile).get()
    },
    dashboardFilesIndex := {
      val distDir = npmBuildTask.value
      val resultFile = (Compile / resourceManaged).value / "dashboard_static_index"
      IO.write(resultFile, dashboardFilesList.value
        .map(file => s"${staticDashboardFilePrefix.value}/${distDir.relativize(file).get.toString}").mkString("\n"))
      resultFile
    },
    dashboardZipArtifact := Artifact(name.value, "zip", "zip"),
    sourceDirectory := baseDirectory.value / "src-scala",
    // Note: resourceGenerators is not run by task compile. It is run by task package or run.
    Compile / resourceGenerators += prefixedDashboardResources.taskValue,
    Compile / resourceGenerators += Def.task { Seq(dashboardFilesIndex.value) }.taskValue,
    cleanFiles += distDirectory.value,
    addArtifact(dashboardZipArtifact, zipDistDirectory)
  )

lazy val `bakery-interaction-protocol`: Project = project.in(file("bakery/interaction-protocol"))
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
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

lazy val `bakery-interaction-k8s-interaction-manager`: Project = project.in(file("bakery/interaction-k8s-interaction-manager"))
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
  .settings(yPartialUnificationSetting)
  .settings(
    moduleName := "bakery-interaction-k8s-interaction-manager",
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
    `baker-interface`,
    `bakery-interaction-protocol`,
    `baker-recipe-compiler`,
    `baker-recipe-dsl`,
    `baker-intermediate-language`,
    `bakery-state`,
    testScope(`bakery-state`),
    testScope(`baker-http-client`),
    testScope(`baker-http-server`)
  )


lazy val `bakery-state`: Project = project.in(file("bakery/state"))
  .enablePlugins(JavaAppPackaging, DockerPlugin)
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
  .settings(yPartialUnificationSetting)
  .settings(
    Compile / mainClass := Some("com.ing.bakery.baker.Main"),
    dockerExposedPorts ++= Seq(8080),
    Docker / packageName := "bakery-state",
    dockerBaseImage := "adoptopenjdk/openjdk11",
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
    `baker-interface`,
    `bakery-interaction-protocol`,
    `baker-recipe-compiler`,
    `baker-recipe-dsl`,
    `baker-intermediate-language`,
    `baker-http-server`,
    `baker-http-dashboard`
  )

lazy val `bakery-interaction`: Project = project.in(file("bakery/interaction"))
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
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
      catsCore
    ) ++ testDeps(
      scalaTest,
      mockitoScala,
      logback
    )
  )
  .dependsOn(`bakery-interaction-protocol`, `baker-interface`)

lazy val `bakery-interaction-spring`: Project = project.in(file("bakery/interaction-spring"))
  .settings(defaultModuleSettings)
  .settings(Publish.settings)
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
    `baker-http-client`,
    `bakery-client-example`,
    `interaction-example-make-payment-and-ship-items`,
    `interaction-example-reserve-items`)

lazy val `baker-example`: Project = project
  .in(file("examples/baker-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(commonSettings)
  .settings(noPublishSettings)
  .settings(yPartialUnificationSetting)
  .settings(crossBuildSettings)
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
        slf4jApi,
        akkaTestKit
      )
  )
  .settings(
    coverageExcludedPackages := "webshop.webservice.recipe;" + // only configuration
      "webshop.webservice.WebShopBaker;webshop.webservice.WebShopService" // example code
  )
  .settings(dockerSettings)
  .settings(
    Docker / packageName := "baker-example-app",
    dockerExposedPorts := Seq(8080)
  )
  .dependsOn(`baker-types`, `baker-akka-runtime`, `baker-recipe-compiler`, `baker-recipe-dsl`, `baker-intermediate-language`)

lazy val `docs-code-snippets`: Project = project
  .in(file("examples/docs-code-snippets"))
  .enablePlugins(JavaAppPackaging)
  .settings(commonSettings)
  .settings(noPublishSettings)
  .settings(yPartialUnificationSetting)
  .settings(crossBuildSettings)
  .settings(
    moduleName := "docs-code-snippets",
    kotlinVersion := "1.8.21",
    kotlincJvmTarget := "17",
    kotlinLib("stdlib-jdk8"),
    kotlinLib("reflect"),
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
        slf4jApi,
        akkaTestKit
      )
  )
  .settings(
    coverageEnabled := false
  )
  .dependsOn(`baker-types`, `baker-akka-runtime`, `baker-recipe-compiler`, `baker-recipe-dsl-kotlin`, `baker-intermediate-language`, `baker-interface-kotlin`)

lazy val `bakery-client-example`: Project = project
  .in(file("examples/bakery-client-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(commonSettings)
  .settings(noPublishSettings)
  .settings(yPartialUnificationSetting)
  .settings(crossBuildSettings)
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
    Docker / packageName := "bakery-client-example",
    coverageEnabled := false
  )
  .dependsOn(`baker-types`, `baker-http-client`, `baker-recipe-compiler`, `baker-recipe-dsl`)

lazy val `bakery-kafka-listener-example`: Project = project
  .in(file("examples/bakery-kafka-listener-example"))
  .enablePlugins(JavaAppPackaging)
  .settings(noPublishSettings)
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
    Docker / packageName := "bakery-kafka-listener-example",
      coverageEnabled := false
  )
  .dependsOn(`baker-types`, `baker-http-client`, `baker-recipe-compiler`, `baker-recipe-dsl`)

lazy val `interaction-example-reserve-items`: Project = project.in(file("examples/bakery-interaction-examples/reserve-items"))
  .enablePlugins(JavaAppPackaging)
  .settings(noPublishSettings)
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
  .settings(coverageEnabled := false)
  .dependsOn(`bakery-interaction`, `baker-recipe-dsl`)

lazy val `interaction-example-make-payment-and-ship-items`: Project = project.in(file("examples/bakery-interaction-examples/make-payment-and-ship-items"))
  .enablePlugins(JavaAppPackaging)
  .settings(noPublishSettings)
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
      ),
    coverageEnabled := false
  )
  .dependsOn(`bakery-interaction`)

