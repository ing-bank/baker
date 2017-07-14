import sbt._

//noinspection TypeAnnotation
object Dependencies {

  val akkaVersion = "2.5.3"
  val kageraVersion = "0.2.24"

  val typeSafeConfig =            "com.typesafe"               %  "config"                             % "1.3.1"

  val akkaInmemoryJournal =      ("com.github.dnvriend"        %% "akka-persistence-inmemory"          % "2.5.1.1")
      .exclude("com.typesafe.akka", "akka-actor")
      .exclude("com.typesafe.akka", "akka-persistence")
      .exclude("com.typesafe.akka", "akka-persistence-query")
      .exclude("com.typesafe.akka", "akka-stream")

  val scalaTest =                 "org.scalatest"              %% "scalatest"                          % "3.0.1"
  val mockito =                   "org.mockito"                %  "mockito-all"                        % "1.10.19"
  val junitInterface =            "com.novocode"               %  "junit-interface"                    % "0.11"

  val akkaActor =                 "com.typesafe.akka"          %% "akka-actor"                         % akkaVersion
  val akkaPersistence =           "com.typesafe.akka"          %% "akka-persistence"                   % akkaVersion
  val akkaCluster =               "com.typesafe.akka"          %% "akka-cluster"                       % akkaVersion
  val akkaClusterSharding =       "com.typesafe.akka"          %% "akka-cluster-sharding"              % akkaVersion
  val akkaSlf4j =                 "com.typesafe.akka"          %% "akka-slf4j"                         % akkaVersion
  val akkaTestKit =               "com.typesafe.akka"          %% "akka-testkit"                       % akkaVersion
  val akkaDistributedData =       "com.typesafe.akka"          %% "akka-distributed-data"              % akkaVersion
  val levelDB   =                 "org.iq80.leveldb"           %  "leveldb"                            % "0.7"
  val levelDBJni =                "org.fusesource.leveldbjni"  %  "leveldbjni-all"                     % "1.8"

  val logback =                   "ch.qos.logback"             %  "logback-classic"                    % "1.2.2"
  val ficusConfig =               "com.iheart"                 %% "ficus"                              % "1.4.0"

  val kagera =                    "io.kagera"                  %% "kagera-api"                         % kageraVersion
  val kageraAkka =                "io.kagera"                  %% "kagera-akka"                        % kageraVersion
  val kageraVisualization =       "io.kagera"                  %% "kagera-visualization"               % kageraVersion

  val scalaReflect =              "org.scala-lang"             %  "scala-reflect"                      % "2.11.8"
  val javaxInject =               "javax.inject"               %  "javax.inject"                       % "1"

  val paranamer =                 "com.thoughtworks.paranamer" %  "paranamer"                          % "2.8"
  val guava =                     "com.google.guava"           %  "guava"                              % "19.0"
  val findbugs =                  "com.google.code.findbugs"   %  "jsr305"                             % "1.3.9"

  val chill =                     "com.twitter"                %% "chill-akka"                         % "0.9.2"
  val kryoSerializers =           "de.javakaffee"              %  "kryo-serializers"                   % "0.41"
  val jodaTime =                  "joda-time"                  %  "joda-time"                          % "2.9.9"
  val jodaConvert =               "org.joda"                   %  "joda-convert"                       % "1.8.1"
  val scalaXml =                  "org.scala-lang.modules"     %% "scala-xml"                          % "1.0.4"
  val slf4jApi =                  "org.slf4j"                  %  "slf4j-api"                          % "1.7.25"
  val scalaCheck =                "org.scalacheck"             %% "scalacheck"                         % "1.13.4"

  def scopeDeps(scope: String, modules: Seq[ModuleID]) =  modules.map(m => m % scope)
  def compileDeps(modules: ModuleID*) = modules.toSeq
  def testDeps(modules: ModuleID*) = scopeDeps("test", modules)
  def providedDeps(modules: ModuleID*) = scopeDeps("provided", modules)
}
