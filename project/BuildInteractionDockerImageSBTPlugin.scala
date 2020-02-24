package baas.sbt

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

    /**
      * Example: "buildInteractionDockerImage docker:publishLocal net.bytebuddy:byte-buddy:1.10.8 Main"
      */
    def buildDockerCommand: Command = Command.args("buildInteractionDockerImage", "<arg>") { (state, args) =>
      args match {
        case commandName :: dependency :: entryPointClassName :: Nil =>
          val moduleID: ModuleID = dependency
            .split(":") match {
            case Array(organization, name, revision) => organization % name % revision
            case other => throw new MessageOnlyException(s"Unexpected dependency declaration $other")
          }

          val stateWithNewDependency =
            Project.extract(state).appendWithSession(Seq(
              libraryDependencies ++= Seq(moduleID),
              packageName in Docker := s"interaction-${entryPointClassName.toLowerCase()}",
              javaOptions in Universal += entryPointClassName
            ), state)

          Command.process(commandName, stateWithNewDependency)
          state
        case _ =>
          throw new MessageOnlyException(s"Expected commandName dependency entryPointClassName")
      }
    }
  }

  import autoImport._

  override lazy val projectSettings: Seq[Def.Setting[_]] = Seq(
    commands += buildDockerCommand
  )
}