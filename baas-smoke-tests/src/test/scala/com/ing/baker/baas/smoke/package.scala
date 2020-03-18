package com.ing.baker.baas

import cats.effect.{IO, Timer}
import cats.syntax.apply._

import scala.concurrent.duration.FiniteDuration

package object smoke {

  def printColor(message: AnyRef, color: String): IO[Unit] =
    IO(println(color + message.toString + Console.RESET))

  def printGreen(message: AnyRef): IO[Unit] =
    printColor(message, Console.GREEN)

  def printCyan(message: AnyRef): IO[Unit] =
    printColor(message, Console.CYAN)

  def printRed(message: AnyRef): IO[Unit] =
    printColor(message, Console.RED)

  def prefix(message: AnyRef, color: String): String =
    "[" + color + message + Console.RESET + "]"

  def prefixGreen(message: AnyRef): String =
    prefix(message, Console.GREEN)

  def prefixCyan(message: AnyRef): String =
    prefix(message, Console.CYAN)

  def prefixRed(message: AnyRef): String =
    prefix(message, Console.RED)

  def within[A](time: FiniteDuration, split: Int)(f: IO[A])(implicit timer: Timer[IO]): IO[A] = {
    def inner(count: Int, times: FiniteDuration): IO[A] = {
      if (count < 1) f else f.attempt.flatMap {
        case Left(_) => IO.sleep(times) *> inner(count - 1, times)
        case Right(a) => IO(a)
      }
    }

    inner(split, time / split)
  }
}
