package baas.sbt

import java.nio.charset.Charset

import com.typesafe.sbt.packager.Keys.packageName
import com.typesafe.sbt.packager.archetypes.JavaAppPackaging
import com.typesafe.sbt.packager.docker.{CmdLike, DockerPlugin, ExecCmd}
import com.typesafe.sbt.packager.docker.DockerPlugin.autoImport._
import com.typesafe.sbt.packager.universal.UniversalPlugin.autoImport._
import kubeyml.deployment.NoProbe
import kubeyml.deployment.plugin.Keys._
import kubeyml.deployment.plugin.KubeDeploymentPlugin
import sbt.Keys._
import sbt._

object BuildInteractionDockerImageSBTPlugin extends sbt.AutoPlugin {

  case class CommandArgumentsBuilder(name: Option[String], publish: Option[String], artifact: Option[String], interactions: List[String])
  case class CommandArguments(name: String, publish: String, artifact: Option[String], interactions: List[String])

  override def requires: Plugins = DockerPlugin && JavaAppPackaging && KubeDeploymentPlugin

  override def trigger: PluginTrigger = allRequirements

  object autoImport {
    val mainClassBody = settingKey[Option[String]]("Main's class source code")

    /**
      * Example: "buildInteractionDockerImage --image-name=<name> --publish=<local|remote> --artifact=net.bytebuddy:byte-buddy:1.10.8 --interaction=path.to.Interaction --interaction=path.to.Interaction2"
      */
    def buildDockerCommand: Command = Command.args("buildInteractionDockerImage", "<arg>") { (state, args) =>

      val NameRegex = """--image-name=(.+)""".r
      val PublishRegex = """--publish=(.+)""".r
      val ArtifactRegex = """--artifact=(.+)""".r
      val InteractionRegex = """--interaction=(.+)""".r

      val builder = args.foldLeft(CommandArgumentsBuilder(None, None, None, List.empty)) { (builder, arg) =>
        arg match {
          case NameRegex(value) => builder.copy(name = Some(value))
          case PublishRegex(value) => builder.copy(publish = Some(value))
          case ArtifactRegex(value) => builder.copy(artifact = Some(value))
          case InteractionRegex(value) => builder.copy(interactions = value :: builder.interactions)
        }
      }

      val arguments = builder match {
        case cmd@CommandArgumentsBuilder(Some(name), Some("local" | "remote") | None, artifact, interactions) if interactions.nonEmpty =>
          CommandArguments(name, cmd.publish.getOrElse("remote"), artifact, interactions)
        case CommandArgumentsBuilder(None, _, _, _) =>
          throw new MessageOnlyException(s"Expected name for image (--image-name=<name>)")
        case CommandArgumentsBuilder(_, _, _, interactions) if interactions.isEmpty =>
          throw new MessageOnlyException(s"Expected at least one interaction (--interaction=<full-class-path>)")
        case _ =>
          throw new MessageOnlyException(s"Expected publish to be either local or remote or empty (--publish=<local|remote>)")
      }

      executeDockerBuild(state, arguments)
    }

    private def executeDockerBuild(state: State, arguments: CommandArguments): State = {
      val moduleID: Option[ModuleID] = arguments.artifact map {
        _.split(":") match {
          case Array(organization, name, revision) => organization % name % revision
          case other => throw new MessageOnlyException(s"Unexpected dependency declaration $other")
        }
      }

      val stateWithNewDependency =
        Project.extract(state).appendWithSession(Seq(
          name := arguments.name,
          libraryDependencies ++= moduleID.toSeq,
          packageName in Docker := arguments.name,
          version in ThisBuild := moduleID.map(_.revision).getOrElse((version in ThisBuild).value),
          javaOptions in Universal += arguments.interactions.mkString(","),
          livenessProbe in kube := NoProbe,
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

      val commandName = arguments.publish match {
        case "local" => "docker:publishLocal"
        case _ => "docker:publish"
      }
      val updatedState = Command.process(commandName, stateWithNewDependency)
      Command.process("kubeyml:gen", updatedState)

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
      |import com.ing.baker.baas.interaction.RemoteInteractionLoader
      |import com.ing.baker.runtime.scaladsl.InteractionInstance
      |
      |import scala.concurrent.ExecutionContext.Implicits.global
      |
      |/**
      |  * Expects single argument containing full classpath entry point for interaction
      |  */
      |object Main extends App {
      |  private def runApp(classNames: String): Unit =
      |    try {
      |      val interactions: List[String] = classNames.split(",").toList
      |      val implementations = interactions
      |        .map(entryClassName => Class.forName(entryClassName).getConstructor().newInstance().asInstanceOf[AnyRef])
      |        .map(implementation => InteractionInstance.unsafeFrom(implementation))
      |      RemoteInteractionLoader.apply(implementations)
      |    } catch {
      |      case ex: Exception =>
      |        throw new IllegalStateException(s"Unable to initialize the classes $classNames", ex)
      |    }
      |
      |  args.headOption.map(runApp).getOrElse(throw new IllegalAccessException("Expected class name a parameter"))
      |}
      |""".stripMargin
}