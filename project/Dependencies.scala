import sbt._

//noinspection TypeAnnotation
object Dependencies {

  val akkaVersion = "2.6.12"
  val akkaManagementVersion = "1.0.9"
  val akkaPersistenceCassandraVersion = "1.0.4"
  val akkaHttpVersion = "10.2.3"
  val http4sVersion = "0.21.18"
  val fs2Version = "2.5.0"
  val circeVersion = "0.13.0"
  val mockitoScalaVersion = "1.16.23"
  val catsVersion = "2.3.1"
  val scalapbVersion = scalapb.compiler.Version.scalapbVersion
  val springVersion = "5.3.3"

  val akkaInmemoryJournal = ("com.github.dnvriend" %% "akka-persistence-inmemory" % "2.5.15.2")
    .exclude("com.typesafe.akka", "akka-actor")
    .exclude("com.typesafe.akka", "akka-persistence")
    .exclude("com.typesafe.akka", "akka-persistence-query")
    .exclude("com.typesafe.akka", "akka-stream")
    .exclude("com.typesafe.akka", "akka-protobuf")

  val scalaJava8Compat = "org.scala-lang.modules" %% "scala-java8-compat" % "0.9.1"
  val scalaTest = "org.scalatest" %% "scalatest" % "3.2.5"
  val mockito = "org.mockito" % "mockito-all" % "1.10.19"
  val mockitoScala = "org.mockito" %% "mockito-scala" % mockitoScalaVersion
  val mockitoScalaTest = "org.mockito" %% "mockito-scala-scalatest" % mockitoScalaVersion
  val mockServer = "org.mock-server" % "mockserver-netty" % "5.11.2"
  val junitInterface = "com.novocode" % "junit-interface" % "0.11"
  val junitJupiter = "org.junit.jupiter" % "junit-jupiter-engine" % "5.7.1"

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
  val akkaHttpSprayJson = "com.typesafe.akka" %% "akka-http-spray-json" % akkaHttpVersion
  val akkaManagementHttp = "com.lightbend.akka.management" %% "akka-management-cluster-http" % akkaManagementVersion
  val akkaClusterBoostrap = "com.lightbend.akka.management" %% "akka-management-cluster-bootstrap" % akkaManagementVersion
  val akkaDiscoveryKube = "com.lightbend.akka.discovery" %% "akka-discovery-kubernetes-api" % akkaManagementVersion

  val scalaKafkaClient = "net.cakesolutions" %% "scala-kafka-client" % "2.3.1"
  val fs2Core = "co.fs2" %% "fs2-core" % fs2Version
  val fs2Io = "co.fs2" %% "fs2-io" % fs2Version
  val fs2kafka = "com.github.fd4s" %% "fs2-kafka" % "1.0.0"
  val levelDB = "org.iq80.leveldb" % "leveldb" % "0.12"

  val levelDBJni = "org.fusesource.leveldbjni" % "leveldbjni-all" % "1.8"

  val ficusConfig = "com.iheart" %% "ficus" % "1.5.0"

  val scalaGraph = "org.scala-graph" %% "graph-core" % "1.13.1"
  val scalaGraphDot = "org.scala-graph" %% "graph-dot" % "1.13.0"
  val graphvizJava = "guru.nidi" % "graphviz-java" % "0.18.0"

  val prometheus = "io.prometheus" % "simpleclient_hotspot" % "0.10.0"
  val prometheusJmx = "io.prometheus.jmx" % "collector" % "0.15.0"
  val sensors =  "nl.pragmasoft.sensors" %% "sensors-core" % "0.0.8"

  val cassandraUnit = "org.cassandraunit" % "cassandra-unit" % "4.3.1.0"
  val cassandraDriverCore = "com.datastax.oss" % "java-driver-core" % "4.10.0"
  val cassandraDriverQueryBuilder = "com.datastax.oss" % "java-driver-query-builder" % "4.10.0"
  val cassandraDriverMetrics = "io.dropwizard.metrics" % "metrics-jmx" % "4.1.16"

  val skuber = "io.skuber" %% "skuber" % "2.6.0"
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

  val catsEffect = "org.typelevel" %% "cats-effect" % catsVersion
  val catsCore = "org.typelevel" %% "cats-core" % catsVersion
  val console4Cats = "dev.profunktor" %% "console4cats" % "0.8.0"
  val catsRetry = "com.github.cb372" %% "cats-retry" % "2.1.0"

  val jnrConstants = "com.github.jnr" % "jnr-constants" % "0.9.9"

  def scalaReflect(scalaV: String): ModuleID = "org.scala-lang" % "scala-reflect" % scalaV

  val javaxInject = "javax.inject" % "javax.inject" % "1"

  val paranamer = "com.thoughtworks.paranamer" % "paranamer" % "2.8"
  val findbugs = "com.google.code.findbugs" % "jsr305" % "1.3.9"

  val scalapbRuntime = "com.thesamet.scalapb" %% "scalapb-runtime" % scalapbVersion % "protobuf"

  val protobufJava = "com.google.protobuf" % "protobuf-java" % "3.14.0"

  val betterFiles = "com.github.pathikrit" %% "better-files" % "3.9.1"

  val typeSafeConfig = "com.typesafe" % "config" % "1.4.1"

  val objenisis = "org.objenesis" % "objenesis" % "3.1"
  val jodaTime = "joda-time" % "joda-time" % "2.10.10"
  val slf4jApi = "org.slf4j" % "slf4j-api" % "1.7.30"
  val logback = "ch.qos.logback" % "logback-classic" % "1.2.3"
  val logstash =  "net.logstash.logback" % "logstash-logback-encoder" % "6.4"
  val scalaCheck = "org.scalacheck" %% "scalacheck" % "1.15.2"
  val scalaCheckPlus = "org.scalatestplus" %% "scalatestplus-scalacheck" % "3.1.0.0-RC2"
  val scalaCheckPlusMockito = "org.scalatestplus" %% "scalatestplus-mockito" % "1.0.0-M2"
  val scalaLogging = "com.typesafe.scala-logging" %% "scala-logging" % "3.9.2"


  val springContext = "org.springframework" % "spring-context" % springVersion
  val springCore = "org.springframework" % "spring-core" % springVersion

  def scopeDeps(scope: String, modules: Seq[ModuleID]) = modules.map(m => m % scope)

  def compileDeps(modules: ModuleID*) = modules.toSeq

  def testDeps(modules: ModuleID*) = scopeDeps("test", modules)

  def providedDeps(modules: ModuleID*) = scopeDeps("provided", modules)
}
