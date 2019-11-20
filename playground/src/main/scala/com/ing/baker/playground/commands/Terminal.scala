package com.ing.baker.playground.commands

import cats.effect.IO

import scala.sys.process._
import com.ing.baker.playground.AppUtils._

object Terminal {

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
  }.app

  def execBlock(command: String): App[String] =
    IO { Process(command).!!<.trim }.app

  def execWithLogger(command: String, logger: ProcessLogger): App[Process] =
    IO { Process(command).run(logger) }.app
}
