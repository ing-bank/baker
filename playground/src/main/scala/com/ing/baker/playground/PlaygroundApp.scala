package com.ing.baker.playground

import cats.implicits._
import cats.effect.IO
import cats.effect.Console.io._
import Command._
import DockerCommands._

import scala.sys.process._

object PlaygroundApp {

  def loop: IO[Unit] =
    for {
      _ <- putStr("playground> ")
      line <- readLn
      _ <- exec(line)
      _ <- if (line == "exit") IO.unit else loop
    } yield ()

  def exec(raw: String): IO[Unit] =
    if (raw == Command.Help.raw)
      commandHelp
    else if (raw == Command.RunCassandra.raw)
      commandRunCassandra.void
    else if (raw == "exit")
      cleanup *> putStrLn("Bye bye! I hope you had fun :D")
    else if (raw == "")
      IO.unit
    else
      putStrLn(s"Unknown command '$raw'")

  def commandHelp: IO[Unit] =
    putStrLn("") *>
    Command.commands.traverse { command =>
      val spaces = List.fill(20 - command.raw.length)(".").mkString
      putStrLn(command.raw + " " + spaces + " " + command.help)
    } *>
    putStrLn("")

  def cassandraName: String = "baker-cassandra"

  def commandRunCassandra: IO[Process] =
    DockerCommands.createDockerNetwork *>
    execPrintAndWaitForMatch(
      process = Process(s"docker run --name $cassandraName --network $networkName -p 9042:9042 -p 9160:9160 cassandra:latest"),
      prompt = "Cassandra",
      condition = _.matches("""INFO  \[OptionalTasks:1\] (.+) CassandraRoleManager\.java:372 - Created default superuser role 'cassandra'""")
    )

  def cleanup: IO[Unit] =
    terminate(cassandraName) *>
    DockerCommands.deleteDockerNetwork.attempt.void
}
