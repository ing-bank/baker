package com.ing.baker.playground

import cats.implicits._
import AppMonad._

object PlaygroundApp {

  def loop: App[Unit] =
    for {
      _ <- print("playground> ")
      line <- readLn
      _ <- exec(line)
      _ <- if (line == "exit") doNothing else loop
    } yield ()

  def exec(raw: String): App[Unit] =
    if (raw == Command.Help.raw)
      commandHelp
    else if (raw == Command.RunCassandra.raw)
      EnvironmentCommands.runCassandra
    else if (raw == Command.RunBaaSStateNode.raw)
      BaaSCommands.runStateNode("3.0.2-SNAPSHOT", 1, "self").void
    else if (raw == Command.StartBaaS.raw)
      BaaSCommands.startBaaS
    else if (raw == "exit")
      cleanup *> printLn("Bye bye! I hope you had fun :D")
    else if (raw == "")
      doNothing
    else
      printLn(s"Unknown command '$raw'")

  def commandHelp: App[Unit] =
    printLn("") *>
    Command.commands.traverse { command =>
      val spaces = List.fill(20 - command.raw.length)(".").mkString
      printLn(command.raw + " " + spaces + " " + command.help)
    } *>
    printLn("")

  def cleanup: App[Unit] =
    DockerCommands.terminateAllImages *>
    DockerCommands.deleteDockerNetwork
}
