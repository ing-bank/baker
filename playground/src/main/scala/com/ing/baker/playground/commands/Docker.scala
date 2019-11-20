package com.ing.baker.playground.commands

import cats.implicits._
import com.ing.baker.playground.AppUtils._

import scala.util.matching.Regex

object Docker {

  def networkName: String = "baker-playground-network"

  def checkForDockerVersion: App[Unit] = {
    val DockerVersionReg: Regex = """Docker version (\d\d).*, build .+""".r
    val requiredVersion: Int = 19
    Terminal.execBlock("docker --version").flatMap {
      case DockerVersionReg(version) =>
        if (version.toInt >= requiredVersion) doNothing
        else fail(s"Docker version is $version but $requiredVersion or greater is required.")
      case _ =>
        fail("Bad input for function isRequiredVersion")
    }
  }

  def terminateAllImages: App[Unit] =
    for {
      env <- getState
      _ <- env.runningImages.traverse(terminate)
      _ <- modify(_.copy(runningImages = List.empty))
    } yield ()

  def terminate(name: String): App[Unit] =
    Terminal.exec(s"docker kill $name", s"Terminate $name").tryForget *>
      Terminal.execBlock(s"docker rm $name").tryForget

  def createDockerNetwork: App[Unit] =
    Terminal.exec(s"docker network create $networkName", "Docker Network").tryForget

  def deleteDockerNetwork: App[Unit] =
    Terminal.exec(s"docker network rm $networkName", "Remove Docker Network").tryForget

  def dockerPull(image: String): App[Unit] =
    Terminal.exec(s"docker pull $image", s"Pull $image Image").void
}
