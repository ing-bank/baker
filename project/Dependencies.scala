import sbt._

//noinspection TypeAnnotation
object Dependencies {

  val akkaVersion = "2.5.29"
  
  val http4sVersion = "0.21.1"
  val circeVersion = "0.13.0"

  val jvmV = "1.8"
  val scalapbVersion = scalapb.compiler.Version.scalapbVersion

  val akkaInmemoryJournal =      ("com.github.dnvriend"        %% "akka-persistence-inmemory"          % "2.5.15.2")
      .exclude("com.typesafe.akka", "akka-actor")
      .exclude("com.typesafe.akka", "akka-persistence")
      .exclude("com.typesafe.akka", "akka-persistence-query")
      .exclude("com.typesafe.akka", "akka-stream")

  val scalaJava8Compat =          "org.scala-lang.modules"     %% "scala-java8-compat"                 % "0.9.1"
  val scalaTest =                 "org.scalatest"              %% "scalatest"                          % "3.0.8"
  val mockito =                   "org.mockito"                %  "mockito-all"                        % "1.10.19"
  val mockServer =                "org.mock-server"            %  "mockserver-netty"                   % "5.9.0"
  val junitInterface =            "com.novocode"               %  "junit-interface"                    % "0.11"
  val junitJupiter =              "org.junit.jupiter"          %  "junit-jupiter-engine"               % "5.6.0"

  val akkaActor =                 "com.typesafe.akka"          %% "akka-actor"                         % akkaVersion
  val akkaStream =                "com.typesafe.akka"          %% "akka-stream"                        % akkaVersion
  val akkaPersistence =           "com.typesafe.akka"          %% "akka-persistence"                   % akkaVersion
  val akkaPersistenceQuery =      "com.typesafe.akka"          %% "akka-persistence-query"             % akkaVersion
  val akkaPersistenceCassandra =  "com.typesafe.akka"          %% "akka-persistence-cassandra"         % "0.103"
  val akkaCluster =               "com.typesafe.akka"          %% "akka-cluster"                       % akkaVersion
  val akkaClusterSharding =       "com.typesafe.akka"          %% "akka-cluster-sharding"              % akkaVersion
  val akkaDistributedData =       "com.typesafe.akka"          %% "akka-distributed-data"              % akkaVersion
  val akkaClusterTools =          "com.typesafe.akka"          %% "akka-cluster-tools"                 % akkaVersion
  val akkaSlf4j =                 "com.typesafe.akka"          %% "akka-slf4j"                         % akkaVersion
  val akkaTestKit =               "com.typesafe.akka"          %% "akka-testkit"                       % akkaVersion
  val akkaStreamTestKit =         "com.typesafe.akka"          %% "akka-stream-testkit"                % akkaVersion
  val akkaMultiNodeTestkit =      "com.typesafe.akka"          %% "akka-multi-node-testkit"            % akkaVersion
  val akkaManagementHttp =        "com.lightbend.akka.management" %% "akka-management-cluster-http"      % "1.0.5"
  val akkaClusterBoostrap =       "com.lightbend.akka.management" %% "akka-management-cluster-bootstrap" % "1.0.5"
  val akkaDiscoveryKube =         "com.lightbend.akka.discovery"  %% "akka-discovery-kubernetes-api"     % "1.0.5"
  val akkaBoostrap =              "com.lightbend.akka.management" %% "akka-management-cluster-bootstrap" % "1.0.5"

  val levelDB   =                 "org.iq80.leveldb"           %  "leveldb"                            % "0.12"

  val levelDBJni =                "org.fusesource.leveldbjni"  %  "leveldbjni-all"                     % "1.8"

  val ficusConfig =               "com.iheart"                 %% "ficus"                              % "1.4.7"

  val scalaGraph  =               "org.scala-graph"            %% "graph-core"                         % "1.11.5"
  val scalaGraphDot =             "org.scala-graph"            %% "graph-dot"                          % "1.11.5"
  val graphvizJava =              "guru.nidi"                  %  "graphviz-java"                      % "0.8.10"

  val kamon =                     "io.kamon"                   %% "kamon-bundle"                       % "2.0.0"
  val kamonAkka =                 "io.kamon"                   %% "kamon-akka"                         % "2.0.0"
  val kamonPrometheus =           "io.kamon"                   %% "kamon-prometheus"                   % "2.0.0"

  val skuber =                    "io.skuber"                  %% "skuber"                             % "2.4.0"
  val http4s =                    "org.http4s"                 %% "http4s-core"                        % http4sVersion
  val http4sDsl =                 "org.http4s"                 %% "http4s-dsl"                         % http4sVersion
  val http4sServer =              "org.http4s"                 %% "http4s-blaze-server"                % http4sVersion
  val http4sClient =              "org.http4s"                 %% "http4s-blaze-client"                % http4sVersion
  val http4sCirce =               "org.http4s"                 %% "http4s-circe"                       % http4sVersion
  val circe =                     "io.circe"                   %% "circe-core"                         % circeVersion
  val circeGeneric =              "io.circe"                   %% "circe-generic"                      % circeVersion

  val catsEffect =                "org.typelevel"              %% "cats-effect"                        % "2.1.2"
  val catsCore =                  "org.typelevel"              %% "cats-core"                          % "2.1.1"
  val console4Cats =              "dev.profunktor"             %% "console4cats"                       % "0.8.0"

  val jnrConstants =              "com.github.jnr"             % "jnr-constants"                       % "0.9.9"

  def scalaReflect(scalaV: String): ModuleID = "org.scala-lang"%  "scala-reflect"                      % scalaV
  val javaxInject =               "javax.inject"               %  "javax.inject"                       % "1"

  val paranamer =                 "com.thoughtworks.paranamer" %  "paranamer"                          % "2.8"
  val findbugs =                  "com.google.code.findbugs"   %  "jsr305"                             % "1.3.9"

  val scalapbRuntime =            "com.thesamet.scalapb"       %% "scalapb-runtime"                    % scalapbVersion % "protobuf"

  val protobufJava =              "com.google.protobuf"        % "protobuf-java"                       % "3.11.4"

  val betterFiles =               "com.github.pathikrit"       %% "better-files"                       % "3.8.0"

  val typeSafeConfig =            "com.typesafe"               % "config"                              % "1.4.0"

  val objenisis =                 "org.objenesis"              %  "objenesis"                          % "3.1"
  val jodaTime =                  "joda-time"                  %  "joda-time"                          % "2.10.5"
  val slf4jApi =                  "org.slf4j"                  %  "slf4j-api"                          % "1.7.30"
  val slf4jSimple =               "org.slf4j"                  % "slf4j-simple"                        % "1.7.30"
  val logback =                   "ch.qos.logback"             % "logback-classic"                     % "1.2.3"
  val scalaCheck =                "org.scalacheck"             %% "scalacheck"                         % "1.13.5"

  val scalaLogging =              "com.typesafe.scala-logging" %% "scala-logging"                      % "3.9.2"

  def scopeDeps(scope: String, modules: Seq[ModuleID]) =  modules.map(m => m % scope)
  def compileDeps(modules: ModuleID*) = modules.toSeq
  def testDeps(modules: ModuleID*) = scopeDeps("test", modules)

  def providedDeps(modules: ModuleID*) = scopeDeps("provided", modules)
}
