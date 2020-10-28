import sbt._

//noinspection TypeAnnotation
object Dependencies {

  val akkaVersion = "2.6.10"
  val akkaManagementVersion = "1.0.9"
  val akkaHttpVersion = "10.2.1"
  val http4sVersion = "0.21.8"
  val circeVersion = "0.13.0"
  val kamonAkkaVersion = "2.1.8"

  val scalapbVersion = scalapb.compiler.Version.scalapbVersion

  val akkaInmemoryJournal = ("com.github.dnvriend" %% "akka-persistence-inmemory" % "2.5.15.2")
    .exclude("com.typesafe.akka", "akka-actor")
    .exclude("com.typesafe.akka", "akka-persistence")
    .exclude("com.typesafe.akka", "akka-persistence-query")
    .exclude("com.typesafe.akka", "akka-stream")
    .exclude("com.typesafe.akka", "akka-protobuf")

  val scalaJava8Compat = "org.scala-lang.modules" %% "scala-java8-compat" % "0.9.1"
  val scalaTest = "org.scalatest" %% "scalatest" % "3.2.2"
  val mockito = "org.mockito" % "mockito-all" % "1.10.19"
  val mockitoScala = "org.mockito" %% "mockito-scala" % "1.16.0"
  val mockitoScalaTest = "org.mockito" %% "mockito-scala-scalatest" % "1.16.0"
  val mockServer = "org.mock-server" % "mockserver-netty" % "5.11.1"
  val junitInterface = "com.novocode" % "junit-interface" % "0.11"
  val junitJupiter = "org.junit.jupiter" % "junit-jupiter-engine" % "5.7.0"

  val akkaActor = "com.typesafe.akka" %% "akka-actor" % akkaVersion

  val akkaStream = "com.typesafe.akka" %% "akka-stream" % akkaVersion
  val akkaProtobuf = "com.typesafe.akka" %% "akka-protobuf" % akkaVersion
  val akkaPersistence = "com.typesafe.akka" %% "akka-persistence" % akkaVersion
  val akkaDiscovery = "com.typesafe.akka" %% "akka-discovery" % akkaVersion
  val akkaPersistenceQuery = "com.typesafe.akka" %% "akka-persistence-query" % akkaVersion
  val akkaPersistenceCassandra = "com.typesafe.akka" %% "akka-persistence-cassandra" % "0.105"
  val akkaCluster = "com.typesafe.akka" %% "akka-cluster" % akkaVersion
  val akkaClusterSharding = "com.typesafe.akka" %% "akka-cluster-sharding" % akkaVersion
  val akkaClusterTools = "com.typesafe.akka" %% "akka-cluster-tools" % akkaVersion
  val akkaSlf4j = "com.typesafe.akka" %% "akka-slf4j" % akkaVersion
  val akkaTestKit = "com.typesafe.akka" %% "akka-testkit" % akkaVersion
  val akkaStreamTestKit = "com.typesafe.akka" %% "akka-stream-testkit" % akkaVersion
  val akkaMultiNodeTestkit = "com.typesafe.akka" %% "akka-multi-node-testkit" % akkaVersion
  val akkaHttpSprayJson = "com.typesafe.akka" %% "akka-http-spray-json" % akkaHttpVersion
  val akkaManagementHttp = "com.lightbend.akka.management" %% "akka-management-cluster-http" % akkaManagementVersion
  val akkaClusterBoostrap = "com.lightbend.akka.management" %% "akka-management-cluster-bootstrap" % akkaManagementVersion
  val akkaDiscoveryKube = "com.lightbend.akka.discovery" %% "akka-discovery-kubernetes-api" % akkaManagementVersion

  val scalaKafkaClient = "net.cakesolutions" %% "scala-kafka-client" % "2.3.1"
  val fs2kafka = "com.github.fd4s" %% "fs2-kafka" % "1.0.0"
  val levelDB = "org.iq80.leveldb" % "leveldb" % "0.12"

  val levelDBJni = "org.fusesource.leveldbjni" % "leveldbjni-all" % "1.8"

  val ficusConfig = "com.iheart" %% "ficus" % "1.5.0"

  val scalaGraph = "org.scala-graph" %% "graph-core" % "1.13.1"
  val scalaGraphDot = "org.scala-graph" %% "graph-dot" % "1.13.0"
  val graphvizJava = "guru.nidi" % "graphviz-java" % "0.17.0"

  val kamon = "io.kamon" %% "kamon-bundle" % kamonAkkaVersion
  val kamonAkka = "io.kamon" %% "kamon-akka" % kamonAkkaVersion
  val kamonPrometheus = "io.kamon" %% "kamon-prometheus" % kamonAkkaVersion

  val skuber = ("io.skuber" %% "skuber" % "2.6.0")
  val play = "com.typesafe.play" %% "play-json" % "2.9.1"

  val http4s = "org.http4s" %% "http4s-core" % http4sVersion
  val http4sDsl = "org.http4s" %% "http4s-dsl" % http4sVersion
  val http4sServer = "org.http4s" %% "http4s-blaze-server" % http4sVersion
  val http4sClient = "org.http4s" %% "http4s-blaze-client" % http4sVersion
  val http4sCirce = "org.http4s" %% "http4s-circe" % http4sVersion
  val circe = "io.circe" %% "circe-core" % circeVersion
  val circeParser = "io.circe" %% "circe-parser" % circeVersion
  val circeGeneric = "io.circe" %% "circe-generic" % circeVersion
  val circeGenericExtras = "io.circe" %% "circe-generic-extras" % circeVersion

  val catsEffect = "org.typelevel" %% "cats-effect" % "2.2.0"
  val catsCore = "org.typelevel" %% "cats-core" % "2.2.0"
  val console4Cats = "dev.profunktor" %% "console4cats" % "0.8.0"
  val catsRetry = "com.github.cb372" %% "cats-retry" % "2.0.0"

  val jnrConstants = "com.github.jnr" % "jnr-constants" % "0.9.9"

  def scalaReflect(scalaV: String): ModuleID = "org.scala-lang" % "scala-reflect" % scalaV

  val javaxInject = "javax.inject" % "javax.inject" % "1"

  val paranamer = "com.thoughtworks.paranamer" % "paranamer" % "2.8"
  val findbugs = "com.google.code.findbugs" % "jsr305" % "1.3.9"

  val scalapbRuntime = "com.thesamet.scalapb" %% "scalapb-runtime" % scalapbVersion % "protobuf"

  val protobufJava = "com.google.protobuf" % "protobuf-java" % "3.13.0"

  val betterFiles = "com.github.pathikrit" %% "better-files" % "3.9.1"

  val typeSafeConfig = "com.typesafe" % "config" % "1.4.1"

  val objenisis = "org.objenesis" % "objenesis" % "3.1"
  val jodaTime = "joda-time" % "joda-time" % "2.10.8"
  val slf4jApi = "org.slf4j" % "slf4j-api" % "1.7.30"
  val logback = "ch.qos.logback" % "logback-classic" % "1.2.3"
  val logstash =  "net.logstash.logback" % "logstash-logback-encoder" % "6.4"
  val scalaCheck = "org.scalacheck" %% "scalacheck" % "1.14.3"
  val scalaCheckPlus = "org.scalatestplus" %% "scalatestplus-scalacheck" % "3.1.0.0-RC2"
  val scalaCheckPlusMockito = "org.scalatestplus" %% "scalatestplus-mockito" % "1.0.0-M2"
  val scalaLogging = "com.typesafe.scala-logging" %% "scala-logging" % "3.9.2"


  val springContext = "org.springframework" % "spring-context" % "5.2.9.RELEASE"
  val springCore = "org.springframework" % "spring-core" % "5.2.9.RELEASE"

  def scopeDeps(scope: String, modules: Seq[ModuleID]) = modules.map(m => m % scope)

  def compileDeps(modules: ModuleID*) = modules.toSeq

  def testDeps(modules: ModuleID*) = scopeDeps("test", modules)

  def providedDeps(modules: ModuleID*) = scopeDeps("provided", modules)
}
