package com.ing.baker.playground

import cats.implicits._
import cats.effect.IO
import Command._
import AppMonad._

import scala.sys.process._
import scala.util.matching.Regex

object DockerCommands {

  def networkName: String = "baker-playground-network"

  def checkForDockerVersion: IO[Unit] = {
    val DockerVersionReg: Regex = """Docker version (\d\d).*, build .+""".r
    val requiredVersion: Int = 19
    execBlock(Process(Seq("docker", "--version"))).map {
      case DockerVersionReg(version) =>
        if (version.toInt >= requiredVersion) IO(())
        else failIO(s"Docker version is $version but $requiredVersion or greater is required.")
      case _ =>
        failIO("Bad input for function isRequiredVersion")
    }
  }

  def terminateAllImages: App[Unit] =
    for {
      env <- getState
      _ <- env.runningImages.traverse(terminate)
      _ <- modify(_.copy(runningImages = List.empty))
    } yield ()

  def terminate(name: String): App[Unit] =
    (execPrint(Process(s"docker kill $name"), s"Terminate $name").attempt.void *>
      execBlock(Process(s"docker rm $name")).attempt.void).app

  def createDockerNetwork: App[Unit] =
    execPrint(Process(s"docker network create $networkName"), "Docker Network").attempt.void.app

  def deleteDockerNetwork: App[Unit] =
    execPrint(Process(s"docker network rm $networkName"), "Remove Docker Network").attempt.void.app

  def dockerPull(image: String): IO[Unit] =
    execPrint(Process(s"docker pull $image"), s"Pull $image Image").void
}
