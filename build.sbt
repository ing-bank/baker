import Dependencies._
import sbt.Def
import sbt.Keys._

val scalaV = "2.11.8"
val jvmV   = "1.8"

val commonSettings = Defaults.coreDefaultSettings ++ Seq(
    organization := "com.ing",
    scalaVersion := scalaV,
    scalacOptions := Seq("-unchecked", "-deprecation", "-encoding", "utf8", s"-target:jvm-$jvmV"),
    javacOptions := Seq("-source", jvmV, "-target", jvmV),
    fork in test := true,
    scalacOptions ++= Seq(
      "-unchecked",
      "-deprecation",
      "-feature",
      "-Ywarn-dead-code",
      "-language:higherKinds",
      "-language:existentials",
      "-language:postfixOps"
    )
  )

lazy val noPublishSettings = Seq(
  publish := (),
  publishLocal := (),
  publishArtifact := false
)

lazy val defaultModuleSettings = commonSettings ++ Revolver.settings ++ SonatypePublish.settings

lazy val baker = project.in(file("core"))
  .settings(defaultModuleSettings: _*)
  .settings(
    moduleName := "baker",
    libraryDependencies ++=
      compileDeps(
        kagera,
        kageraAkka,
        kageraVisualization,
        akkaPersistence,
        akkaActor,
        akkaCluster,
        akkaClusterSharding,
        scalaReflect,
        javaxInject,
        paranamer,
        typeSafeConfig,
        ficusConfig,
        akkaInmemoryJournal,
        guava,
        chill,
        kryoSerializers,
        jodaTime,
        jodaConvert
      ) ++
      testDeps(
        akkaSlf4j,
        akkaTestKit,
        logback,
        mockito,
        scalaTest,
        junit,
        levelDB,
        levelDBJni
      ) ++
      providedDeps(
        findbugs
      ))

lazy val root = project
  .in(file("."))
  .aggregate(baker)
  .dependsOn(baker)
  .settings(defaultModuleSettings)
  .settings(noPublishSettings)

//lazy val micrositeSettings = Seq(
//  micrositeName := "Baker",
//  micrositeDescription := "Bake your process",
//  micrositeBaseUrl := "baker",
//  micrositeDocumentationUrl := "/baker/docs.html",
//  micrositeGithubOwner := "ing-bank",
//  micrositeGithubRepo := "baker",
//  micrositeHighlightTheme := "tomorrow",
//  micrositePalette := Map("brand-primary"   -> "#FF518C",
//                          "brand-secondary" -> "#2F2859",
//                          "brand-tertiary"  -> "#28224C",
//                          "gray-dark"       -> "#48474C",
//                          "gray"            -> "#8D8C92",
//                          "gray-light"      -> "#E3E2E3",
//                          "gray-lighter"    -> "#F4F3F9",
//                          "white-color"     -> "#FFFFFF"),
//  includeFilter in makeSite := "*.html" | "*.css" | "*.png" | "*.jpg" | "*.gif" | "*.js" | "*.swf" | "*.md"
//)
//
//lazy val docsSettings = basicSettings ++ micrositeSettings ++ Seq(
//    tutScalacOptions ~= (_.filterNot(Set("-Ywarn-unused-import", "-Ywarn-dead-code"))),
//    tutScalacOptions ++= (scalaBinaryVersion.value match {
//    case "2.10" => Seq("-Xdivergence211")
//    case _      => Nil
//  }),
//    aggregate in doc := true
//  )
//
//lazy val docs = project
//  .in(file("docs"))
//  .dependsOn(baker)
//  .settings(moduleName := "baker-docs")
//  .settings(docsSettings: _*)
//  .settings(noPublishSettings)
//  .enablePlugins(MicrositesPlugin)
//

