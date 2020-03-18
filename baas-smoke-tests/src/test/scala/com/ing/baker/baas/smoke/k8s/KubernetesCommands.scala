package com.ing.baker.baas.smoke.k8s

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.smoke.printGreen

import scala.sys.process._

object KubernetesCommands {

  def exec(prefix: String, command: String): IO[Int] = {

    def processLogger(prefix: String): ProcessLogger = ProcessLogger(
      line => println(prefix + " " + line),
      err => stderr.println(Console.RED + err + Console.RESET))

    IO(command.!(processLogger(prefix)))
  }

  def basicSetup(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Namespace] =
    for {
      namespace <- Namespace.resource
      _ <- Resource.liftF(printGreen(s"\nCreating Bakery cluster environment."))
      _ <- DefinitionFile.resource("crd-recipe.yaml")
      _ <- DefinitionFile.resource("bakery-controller.yaml", namespace)
      _ <- Resource.liftF(Pod.awaitForAllPods(namespace))
    } yield namespace
}
