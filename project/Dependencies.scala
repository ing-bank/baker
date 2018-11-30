import sbt._

//noinspection TypeAnnotation
object Dependencies {

  val akkaVersion = "2.5.17"
  val jvmV = "1.8"
  val scalapbVersion = scalapb.compiler.Version.scalapbVersion

  val typeSafeConfig =            "com.typesafe"               %  "config"                             % "1.3.1"

  val akkaInmemoryJournal =      ("com.github.dnvriend"        %% "akka-persistence-inmemory"          % "2.5.1.1")
      .exclude("com.typesafe.akka", "akka-actor")
      .exclude("com.typesafe.akka", "akka-persistence")
      .exclude("com.typesafe.akka", "akka-persistence-query")
      .exclude("com.typesafe.akka", "akka-stream")

  val scalaTest =                 "org.scalatest"              %% "scalatest"                          % "3.0.5"
  val mockito =                   "org.mockito"                %  "mockito-all"                        % "1.10.19"
  val junitInterface =            "com.novocode"               %  "junit-interface"                    % "0.11"

  val akkaActor =                 "com.typesafe.akka"          %% "akka-actor"                         % akkaVersion
  val akkaStream =                "com.typesafe.akka"          %% "akka-stream"                        % akkaVersion
  val akkaPersistence =           "com.typesafe.akka"          %% "akka-persistence"                   % akkaVersion
  val akkaPersistenceQuery =      "com.typesafe.akka"          %% "akka-persistence-query"             % akkaVersion
  val akkaPersistenceCassandra =  "com.typesafe.akka"          %% "akka-persistence-cassandra"         % "0.54"
  val akkaCluster =               "com.typesafe.akka"          %% "akka-cluster"                       % akkaVersion
  val akkaClusterSharding =       "com.typesafe.akka"          %% "akka-cluster-sharding"              % akkaVersion
  val akkaSlf4j =                 "com.typesafe.akka"          %% "akka-slf4j"                         % akkaVersion
  val akkaTestKit =               "com.typesafe.akka"          %% "akka-testkit"                       % akkaVersion
  val akkaStreamTestKit =         "com.typesafe.akka"          %% "akka-stream-testkit"                % akkaVersion
  val akkaMultiNodeTestkit =      "com.typesafe.akka"          %% "akka-multi-node-testkit"            % akkaVersion
  val akkaHttp =                  "com.typesafe.akka"          %% "akka-http"                          % "10.0.10"
  val levelDB   =                 "org.iq80.leveldb"           %  "leveldb"                            % "0.7"
  val levelDBJni =                "org.fusesource.leveldbjni"  %  "leveldbjni-all"                     % "1.8"

  val logback =                   "ch.qos.logback"             %  "logback-classic"                    % "1.2.2"
  val ficusConfig =               "com.iheart"                 %% "ficus"                              % "1.4.0"

  val scalaGraph  =               "org.scala-graph"            %% "graph-core"                         % "1.11.5"
  val scalaGraphDot =             "org.scala-graph"            %% "graph-dot"                          % "1.11.5"
  val graphvizJava =              "guru.nidi"                  %  "graphviz-java"                      % "0.8.0"

  val catsEffect =                "org.typelevel"              %% "cats-effect"                        % "0.10"
  val catsCore =                  "org.typelevel"              %% "cats-core"                          % "1.1.0"

  def scalaReflect(scalaV: String): ModuleID = "org.scala-lang"%  "scala-reflect"                      % scalaV
  val javaxInject =               "javax.inject"               %  "javax.inject"                       % "1"

  val paranamer =                 "com.thoughtworks.paranamer" %  "paranamer"                          % "2.8"
  val guava =                     "com.google.guava"           %  "guava"                              % "19.0"
  val findbugs =                  "com.google.code.findbugs"   %  "jsr305"                             % "1.3.9"

  val scalapbRuntime =            "com.thesamet.scalapb"       %% "scalapb-runtime"                    % scalapbVersion % "protobuf"
  val chill =                    ("com.twitter"                %% "chill-akka"                         % "0.9.2")
    .exclude("com.typesafe.akka", "akka-actor")

  val kryo =                      "com.esotericsoftware"       % "kryo"                                % "4.0.0"

  val protobufJava =              "com.google.protobuf"        % "protobuf-java"                       % "3.5.1"

  val betterFiles =               "com.github.pathikrit"       %% "better-files"                       % "3.6.0"

  val kryoSerializers =           "de.javakaffee"              %  "kryo-serializers"                   % "0.41"
  val objenisis =                 "org.objenesis"              %  "objenesis"                          % "2.5.1"

  val jodaTime =                  "joda-time"                  %  "joda-time"                          % "2.9.9"
  val slf4jApi =                  "org.slf4j"                  %  "slf4j-api"                          % "1.7.25"
  val scalaCheck =                "org.scalacheck"             %% "scalacheck"                         % "1.13.4"

  def scopeDeps(scope: String, modules: Seq[ModuleID]) =  modules.map(m => m % scope)
  def compileDeps(modules: ModuleID*) = modules.toSeq
  def testDeps(modules: ModuleID*) = scopeDeps("test", modules)

  def providedDeps(modules: ModuleID*) = scopeDeps("provided", modules)
}
