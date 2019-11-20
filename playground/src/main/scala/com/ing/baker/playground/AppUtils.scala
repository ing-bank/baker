package com.ing.baker.playground

import cats.Show
import cats.data.StateT
import cats.effect.IO
import cats.implicits._
import cats.effect.Console.{io => console}

import scala.util.Random

object AppUtils {

  case class Environment(runningImages: List[String])

  type App[A] = StateT[IO, Environment, A]

  implicit class AppIO[A](io: IO[A]) {

    def app: App[A] = StateT.liftF(io)
  }

  implicit class AppOps[A](app: App[A]) {

    def tryForget: App[Unit] =
      AppUtils.tryForget(app)
  }

  def pure[A](a: A): App[A] = StateT.pure(a)

  def fail[A](e: Throwable): App[A] = IO.raiseError(e).app

  def fail[A](e: String): App[A] = IO.raiseError(new Exception(e)).app

  def tryForget[A](program: App[A]): App[Unit] =
    StateT { state => program.run(state).attempt.map(_ => state -> ()) }

  def modify(f: Environment => Environment): App[Unit] =
    StateT.modify[IO, Environment](f)

  def getState: App[Environment] =
    StateT.get[IO, Environment]

  def addRunningImage(imageName: String): App[Unit] =
    modify(state => state.copy(runningImages = imageName :: state.runningImages))

  def doNothing: App[Unit] =
    StateT.pure[IO, Environment, Unit](())

  def print(message: String): App[Unit] =
    console.putStr(message).app

  def printLn(message: String): App[Unit] =
    console.putStrLn(message).app

  def printLnA[A: Show](a: A): App[Unit] =
    print(a.show)

  def readLn: App[String] =
    console.readLn.app

  private val colors: Array[String] = Array(
    Console.MAGENTA,
    Console.RED,
    Console.YELLOW,
    Console.GREEN,
    Console.CYAN,
    Console.BLUE
  )

  implicit class PrettyColorPrint[A](a: A) {

    def print: IO[Unit] =
      IO { println(a.toString) }

    def magenta: String =
      Console.MAGENTA + a.toString + Console.RESET

    def green: String =
      Console.GREEN + a.toString + Console.RESET

    def red: String =
      Console.RED + a.toString + Console.RESET

    def yellow: String =
      Console.YELLOW + a.toString + Console.RESET

    def randomColor: String =
      colors(Random.nextInt(colors.length)) + a.toString + Console.RESET

    def prompt(prepend: String): String =
      a.toString.lines.map(prepend + _).mkString("\n")

    def notice: String =
      " [>>>] " + a.toString + " [<<<] "
  }
}
