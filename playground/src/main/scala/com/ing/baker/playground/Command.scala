package com.ing.baker.playground

import cats.effect.IO
import ColorPrint._
import scala.sys.process._

trait Command {

  def raw: String = "unmatched command, fix me"

  def help: String = "No help for this command"
}

object Command {

  val commands: List[Command] =
    List(
      Help,
      RunCassandra,
      RunBaaSStateNode,
      StartBaaS
    )

  case object Help extends Command {

    override def raw: String = "help"

    override def help: String = "Displays this help menu"
  }

  case object RunCassandra extends Command {

    override def raw: String = "run-cassandra"

    override def help: String = "Runs Cassandra on default ports within the playground network"
  }

  case object RunBaaSStateNode extends Command {

    override def raw: String = "run-baas-state-node"

    override def help: String = "Runs a single BaaS state node (the one with the http server and state of the recipe instance) within the playground network"
  }

  case object StartBaaS extends Command {

    override def raw: String = "start-baas"

    override def help: String = "Starts Cassandra, Haproxy and a cluster of 3 baas state nodes"
  }

  def execPrint(process: ProcessBuilder, prompt: String): IO[Unit] = {
    val p = prompt.randomColor
    exec(process, ProcessLogger(
      _.prompt(p + " | ").print.unsafeRunSync(),
      _.prompt((prompt + " [ERROR]").red + " | ").print.unsafeRunSync()
    )).flatMap { running =>
      val exitValue = running.exitValue()
      if (exitValue == 0) IO(())
      else IO.raiseError(new Exception(s"Command $process exited with non zero value $exitValue"))
    }
  }

  def execPrintAndWaitForMatch(process: ProcessBuilder, prompt: String, condition: String => Boolean): IO[Process] = {
    IO.async { callback =>
      val p = prompt.randomColor
      var running: Process = null
      var matched: Boolean = false
      running = process.run(ProcessLogger(
        { line =>
          line.prompt(p + " | ").print.unsafeRunSync()
          if(condition(line) && !matched) {
            matched = true
            callback(Right(running))
          }
        },
        { line =>
          line.prompt((prompt + " [ERROR]").red + " | ").print.unsafeRunSync()
          if(condition(line) && !matched) {
            matched = true
            callback(Right(running))
          }
        }
      ))
    }
  }

  def execBlock(process: ProcessBuilder): IO[String] =
    IO { process.!!<.trim }

  def exec(process: ProcessBuilder, logger: ProcessLogger): IO[Process] =
    IO { process.run(logger) }

  def failIO(reason: String): IO[Nothing] =
    IO.raiseError(new Exception(reason))
}
