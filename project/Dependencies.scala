import sbt._

//noinspection TypeAnnotation
object Dependencies {

  val akkaVersion = "2.6.19"
  val akkaManagementVersion = "1.1.3"
  val akkaPersistenceCassandraVersion = "1.0.5"
  val akkaHttpVersion = "10.2.9"
  val http4sVersion = "0.21.33"
  val fs2Version = "2.5.10"
  val circeVersion = "0.14.3"
  val mockitoScalaVersion = "1.17.7"
  val catsEffectVersion = "2.5.5"
  val catsCoreVersion = "2.8.0"
  val scalapbVersion = scalapb.compiler.Version.scalapbVersion
  val springVersion = "5.3.22"
  val springBootVersion = "2.6.1"

  val akkaInmemoryJournal = ("com.github.dnvriend" %% "akka-persistence-inmemory" % "2.5.15.2")
    .exclude("com.typesafe.akka", "akka-actor")
    .exclude("com.typesafe.akka", "akka-persistence")
    .exclude("com.typesafe.akka", "akka-persistence-query")
    .exclude("com.typesafe.akka", "akka-stream")
    .exclude("com.typesafe.akka", "akka-protobuf")

  val scalaJava8Compat100 = "org.scala-lang.modules" %% "scala-java8-compat" % "1.0.0"
  val scalaJava8Compat091 = "org.scala-lang.modules" %% "scala-java8-compat" % "0.9.1"

  val scalaTest = "org.scalatest" %% "scalatest" % "3.2.12"
  val mockitoScala = "org.mockito" %% "mockito-scala" % mockitoScalaVersion
  val mockitoScalaTest = "org.mockito" %% "mockito-scala-scalatest" % mockitoScalaVersion
  val mockServer = "org.mock-server" % "mockserver-netty" % "5.13.2"
  val junitInterface = "com.github.sbt" % "junit-interface" % "0.13.3"
  val junitJupiter = "org.junit.jupiter" % "junit-jupiter-engine" % "5.8.2"

  val akkaActor = "com.typesafe.akka" %% "akka-actor" % akkaVersion

  val akkaStream = "com.typesafe.akka" %% "akka-stream" % akkaVersion
  val akkaProtobuf = "com.typesafe.akka" %% "akka-protobuf" % akkaVersion
  val akkaPersistence = "com.typesafe.akka" %% "akka-persistence" % akkaVersion
  val akkaDiscovery = "com.typesafe.akka" %% "akka-discovery" % akkaVersion
  val akkaPersistenceQuery = "com.typesafe.akka" %% "akka-persistence-query" % akkaVersion
  val akkaPersistenceCassandra = "com.typesafe.akka" %% "akka-persistence-cassandra" % akkaPersistenceCassandraVersion
  val akkaCluster = "com.typesafe.akka" %% "akka-cluster" % akkaVersion
  val akkaClusterSharding = "com.typesafe.akka" %% "akka-cluster-sharding" % akkaVersion
  val akkaClusterTools = "com.typesafe.akka" %% "akka-cluster-tools" % akkaVersion
  val akkaClusterMetrics = "com.typesafe.akka" %% "akka-cluster-metrics" % akkaVersion
  val akkaSlf4j = "com.typesafe.akka" %% "akka-slf4j" % akkaVersion
  val akkaTestKit = "com.typesafe.akka" %% "akka-testkit" % akkaVersion
  val akkaStreamTestKit = "com.typesafe.akka" %% "akka-stream-testkit" % akkaVersion
  val akkaMultiNodeTestkit = "com.typesafe.akka" %% "akka-multi-node-testkit" % akkaVersion
  val akkaPki = "com.typesafe.akka" %% "akka-pki" % akkaVersion
  val akkaActorTyped = "com.typesafe.akka" %% "akka-actor-typed" % akkaVersion
  val akkaClusterTyped = "com.typesafe.akka" %% "akka-cluster-typed" % akkaVersion
  val akkaPersistenceTyped = "com.typesafe.akka" %% "akka-persistence-typed" % akkaVersion
  val akkaStreamTyped = "com.typesafe.akka" %% "akka-stream-typed" % akkaVersion
  val akkaHttpSprayJson = "com.typesafe.akka" %% "akka-http-spray-json" % akkaHttpVersion
  val akkaManagementHttp = "com.lightbend.akka.management" %% "akka-management-cluster-http" % akkaManagementVersion
  val akkaClusterBoostrap = "com.lightbend.akka.management" %% "akka-management-cluster-bootstrap" % akkaManagementVersion
  val akkaDiscoveryKube = "com.lightbend.akka.discovery" %% "akka-discovery-kubernetes-api" % akkaManagementVersion

  val kafkaClient = "org.apache.kafka" % "kafka-clients" % "3.2.0"
  val fs2Core = "co.fs2" %% "fs2-core" % fs2Version
  val fs2Io = "co.fs2" %% "fs2-io" % fs2Version
  val fs2kafka = "com.github.fd4s" %% "fs2-kafka" % "1.0.0"
  val levelDB = "org.iq80.leveldb" % "leveldb" % "0.12"

  val levelDBJni = "org.fusesource.leveldbjni" % "leveldbjni-all" % "1.8"

  val ficusConfig = "com.iheart" %% "ficus" % "1.5.2"

  val scalaGraph = "org.scala-graph" %% "graph-core" % "1.13.1"
  val scalaGraphDot = "org.scala-graph" %% "graph-dot" % "1.13.0"
  val graphvizJava = "guru.nidi" % "graphviz-java" % "0.18.1"

  val prometheus = "io.prometheus" % "simpleclient_hotspot" % "0.16.0"
  val prometheusJmx = "io.prometheus.jmx" % "collector" % "0.17.0"
  val sensors =  "nl.pragmasoft.sensors" %% "sensors-core" % "0.3.0"

  val cassandraUnit = "org.cassandraunit" % "cassandra-unit" % "4.3.1.0"
  val cassandraDriverCore = "com.datastax.oss" % "java-driver-core" % "4.14.1"
  val cassandraDriverQueryBuilder = "com.datastax.oss" % "java-driver-query-builder" % "4.14.1"
  val cassandraDriverMetrics = "io.dropwizard.metrics" % "metrics-jmx" % "4.2.10"

  val skuber = "io.skuber" %% "skuber" % "2.6.4"
  val play = "com.typesafe.play" %% "play-json" % "2.9.2"

  val http4s = "org.http4s" %% "http4s-core" % http4sVersion
  val http4sDsl = "org.http4s" %% "http4s-dsl" % http4sVersion
  val http4sServer = "org.http4s" %% "http4s-blaze-server" % http4sVersion
  val http4sClient = "org.http4s" %% "http4s-blaze-client" % http4sVersion
  val http4sCirce = "org.http4s" %% "http4s-circe" % http4sVersion
  val http4sPrometheus =  "org.http4s" %% "http4s-prometheus-metrics" % http4sVersion
  val circe = "io.circe" %% "circe-core" % circeVersion
  val circeParser = "io.circe" %% "circe-parser" % circeVersion
  val circeGeneric = "io.circe" %% "circe-generic" % circeVersion
  val circeGenericExtras = "io.circe" %% "circe-generic-extras" % circeVersion

  val catsEffect = "org.typelevel" %% "cats-effect" % catsEffectVersion
  val catsEffectTesting = "com.codecommit" %% "cats-effect-testing-scalatest" % "0.5.4"
  val catsCore = "org.typelevel" %% "cats-core" % catsCoreVersion
  val console4Cats = "dev.profunktor" %% "console4cats" % "0.8.0"
  val catsRetry = "com.github.cb372" %% "cats-retry" % "2.1.1"

  val jnrConstants = "com.github.jnr" % "jnr-constants" % "0.9.9"

  def scalaReflect(scalaV: String): ModuleID = "org.scala-lang" % "scala-reflect" % scalaV

  val javaxInject = "javax.inject" % "javax.inject" % "1"

  val paranamer = "com.thoughtworks.paranamer" % "paranamer" % "2.8"
  val findbugs = "com.google.code.findbugs" % "jsr305" % "1.3.9"

  val scalapbRuntime = "com.thesamet.scalapb" %% "scalapb-runtime" % scalapbVersion % "protobuf"

  val protobufJava = "com.google.protobuf" % "protobuf-java" % "3.21.2"

  val betterFiles = "com.github.pathikrit" %% "better-files" % "3.9.1"

  val typeSafeConfig = "com.typesafe" % "config" % "1.4.2"

  val objenisis = "org.objenesis" % "objenesis" % "3.2"
  val jodaTime = "joda-time" % "joda-time" % "2.10.14"
  val slf4jApi = "org.slf4j" % "slf4j-api" % "1.7.36"
  val logback = "ch.qos.logback" % "logback-classic" % "1.2.11"
  val logstash =  "net.logstash.logback" % "logstash-logback-encoder" % "6.4"
  val scalaCheck = "org.scalacheck" %% "scalacheck" % "1.16.0"
  val scalaCheckPlus = "org.scalatestplus" %% "scalacheck-1-15" % "3.2.11.0"
  val scalaCheckPlusMockito = "org.scalatestplus" %% "mockito-3-12" % "3.2.10.0"
  val scalaLogging = "com.typesafe.scala-logging" %% "scala-logging" % "3.9.5"


  val springContext = "org.springframework" % "spring-context" % springVersion
  val springCore = "org.springframework" % "spring-core" % springVersion
  val springBootStarter = "org.springframework.boot" % "spring-boot-starter" % springBootVersion

  val snakeYaml = "org.yaml" % "snakeyaml" % "1.31"

  val jacksonDatabind = "com.fasterxml.jackson.core" % "jackson-databind" % "2.13.3"
  val jacksonCore = "com.fasterxml.jackson.core" % "jackson-core" % "2.13.3"
  val jawnParser = "org.typelevel" %% "jawn-parser" % "1.4.0"
  val nettyHandler = "io.netty" % "netty-handler" % "4.1.81.Final"

  private val bouncycastleVersion = "1.70"

  val bouncyCastleBcprov = "org.bouncycastle" % "bcprov-jdk15on" % bouncycastleVersion
  val bouncyCastleBcpkix ="org.bouncycastle" % "bcpkix-jdk15on" % bouncycastleVersion

  val guava = "com.google.guava" % "guava" % "31.1-jre"

  def scopeDeps(scope: String, modules: Seq[ModuleID]) = modules.map(m => m % scope)

  def compileDeps(modules: ModuleID*) = modules.toSeq

  def testDeps(modules: ModuleID*) = scopeDeps("test", modules)

  def providedDeps(modules: ModuleID*) = scopeDeps("provided", modules)
}
