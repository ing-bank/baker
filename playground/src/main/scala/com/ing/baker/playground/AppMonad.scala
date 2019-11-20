package com.ing.baker.playground

import cats.Show
import cats.data.StateT
import cats.effect.IO
import cats.implicits._
import cats.effect.Console.{ io => console }

object AppMonad {

  case class Environment(runningImages: List[String])

  type App[A] = StateT[IO, Environment, A]

  implicit class AppIO[A](io: IO[A]) {

    def app: App[A] = StateT.liftF(io)
  }

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
}
