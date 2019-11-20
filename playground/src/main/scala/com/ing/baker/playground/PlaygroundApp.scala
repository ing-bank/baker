package com.ing.baker.playground

import cats.implicits._
import com.ing.baker.playground.AppUtils._
import com.ing.baker.playground.Command.RunCommand
import com.ing.baker.playground.commands.Docker

object PlaygroundApp {

  def loop: App[Unit] =
    for {
      _ <- print("playground> ")
      line <- readLn
      _ <- exec(line)
      _ <- if (line == "exit") doNothing else loop
    } yield ()

  def exec(raw: String): App[Unit] =
    tryOneCommand.applyOrElse(raw, other => printLn(s"Unknown command '$other'"))

  def tryOneCommand: RunCommand =
    Command.commands.foldRight({
      case "exit" =>
        cleanup *> printLn("Bye bye! I hope you had fun :D")
      case "clean" =>
        cleanup *> printLn("Clean")
      case "" =>
        doNothing
    })(_.run.orElse(_))

  def cleanup: App[Unit] =
    Docker.terminateAllImages *>
    Docker.deleteDockerNetwork
}
