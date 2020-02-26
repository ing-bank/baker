package baas.sbt

import java.nio.charset.Charset

import com.typesafe.sbt.packager.Keys.packageName
import com.typesafe.sbt.packager.archetypes.JavaAppPackaging
import com.typesafe.sbt.packager.docker.DockerPlugin
import com.typesafe.sbt.packager.docker.DockerPlugin.autoImport._
import com.typesafe.sbt.packager.universal.UniversalPlugin.autoImport._
import sbt.Keys._
import sbt._


object BuildInteractionDockerImageSBTPlugin extends sbt.AutoPlugin {
  override def requires: Plugins = DockerPlugin && JavaAppPackaging

  override def trigger: PluginTrigger = allRequirements

  object autoImport {
    val mainClassBody = settingKey[Option[String]]("Main's class source code")

    /**
      * Example: "buildInteractionDockerImage docker:publishLocal net.bytebuddy:byte-buddy:1.10.8 Main"
      */
    def buildDockerCommand: Command = Command.args("buildInteractionDockerImage", "<arg>") { (state, args) =>
      args match {
        case commandName :: dependency :: entryPointClassName :: Nil =>
          executeDockerBuild(state, commandName, Some(dependency), entryPointClassName)
        case commandName :: entryPointClassName :: Nil =>
          executeDockerBuild(state, commandName, None, entryPointClassName)
        case _ =>
          throw new MessageOnlyException(s"Expected commandName dependency entryPointClassName")
      }
    }

    private def executeDockerBuild(state: State,
                                   commandName: String,
                                   dependency: Option[String],
                                   entryPointClassName: String): State = {
      val moduleID: Option[ModuleID] = dependency map {
        _.split(":") match {
          case Array(organization, name, revision) => organization % name % revision
          case other => throw new MessageOnlyException(s"Unexpected dependency declaration $other")
        }
      }

      val stateWithNewDependency =
        Project.extract(state).appendWithSession(Seq(
          libraryDependencies ++= moduleID.toSeq,
          packageName in Docker := s"interaction-${entryPointClassName.toLowerCase()}",
          javaOptions in Universal += entryPointClassName,
          sourceGenerators in Compile += Def.task {
            val mainClassName =
              (mainClass in Compile).value.getOrElse(throw new MessageOnlyException("mainClass in Compile is required"))

            val pathList = mainClassName.split("\\.")

            val file =
              (pathList.dropRight(1) :+ pathList.last + ".scala")
                .foldLeft((sourceManaged in Compile).value) {
                  case (file, subPath) => file / subPath
                }

            val sourceBytes = mainClassBody.value.getOrElse(mainClassBodyDefault).getBytes(Charset.defaultCharset())
            IO.write(file, sourceBytes)
            Seq(file)
          }.taskValue
        ), state)

      Command.process(commandName, stateWithNewDependency)

      state
    }
  }

  import autoImport._

  override lazy val projectSettings: Seq[Def.Setting[_]] = Seq(
    mainClassBody := None,
    mainClass in Compile := Some("com.ing.baker.baas.Main"),
    commands += buildDockerCommand
  )

  private val mainClassBodyDefault =
    """
      |package com.ing.baker.baas
      |
      |import com.ing.baker.baas.scaladsl.RemoteInteraction
      |import com.ing.baker.runtime.scaladsl.InteractionInstance
      |
      |import scala.concurrent.ExecutionContext.Implicits.global
      |
      |/**
      |  * Expects single argument containing full classpath entry point for interaction
      |  */
      |object Main extends App {
      |  private def runApp(entryClassName: String): Unit =
      |    try {
      |      val implementation = Class.forName(entryClassName).newInstance.asInstanceOf[AnyRef]
      |      RemoteInteraction.load(InteractionInstance.unsafeFrom(implementation))
      |    } catch {
      |      case ex: Exception =>
      |        throw new IllegalStateException(s"Unable to initialize the class name $entryClassName", ex)
      |    }
      |
      |  args.headOption.map(runApp).getOrElse(throw new IllegalAccessException("Expected class name a parameter"))
      |}
      |""".stripMargin
}