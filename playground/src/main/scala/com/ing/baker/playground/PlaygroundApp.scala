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
    tryOneCommand
      .applyOrElse(raw, (other: String) => printLn(s"Unknown command '$other'"))
      .attempt
      .flatMap {
        case Left(e) => printLn(e.getMessage)
        case Right(_) => doNothing
      }

  def tryOneCommand: RunCommand =
    Command.commands.foldRight[RunCommand]({
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
