package com.ing.baker.playground.commands

import cats.implicits._
import cats.effect.IO

import scala.sys.process._
import com.ing.baker.playground.AppUtils._

object Terminal {

  def moveToBakerLocation: App[Unit] = {
    for {
      state <- getState
      location <- state.bakerLocation match {
        case None => confirmBakerProjectLocation
        case Some(location0) => pure(location0)
      }
      _ <- cd(location)
    } yield ()
  }

  private def confirmBakerProjectLocation: App[String] = {
    def confirm(path: String): App[String] =
      for {
        answer <- query(s"Is $path the baker project location? input yes or the correct absolute path")
        realPath <- answer match {
          case "yes" | "y" | "ye" =>
            pure(path)
          case path0 =>
            confirm(path0)
        }
      } yield realPath
    pwd >>= confirm
  }

  def pwd: App[String] =
    execBlock("pwd")

  def cd(location: String): App[Unit] =
    execBlock(s"cd $location").attempt.flatMap {
      case Left(e) =>
        fail(s"Could not move to directory $location... reason: ${e.getMessage}")
      case Right(_) =>
        doNothing
    }

  def query(question: String): App[String] =
    printLn(question + ": ") *> readLn

  def exec(command: String, prompt: String): App[Unit] = {
    val p = prompt.randomColor
    execWithLogger(command, ProcessLogger(
      _.prompt(p + " | ").print.unsafeRunSync(),
      _.prompt((prompt + " [ERROR]").red + " | ").print.unsafeRunSync()
    )).flatMap { running =>
      val exitValue = running.exitValue()
      if (exitValue == 0) doNothing
      else fail(new Exception(s"Command $command exited with non zero value $exitValue"))
    }
  }

  def execAndWait(command: String, prompt: String, condition: String => Boolean): App[Process] = {
    val process = Process(command)
    IO.async[Process] { callback =>
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
  }.app

  def execBlock(command: String): App[String] =
    IO { Process(command).!!<.trim }.app

  def execWithLogger(command: String, logger: ProcessLogger): App[Process] =
    IO { Process(command).run(logger) }.app
}
