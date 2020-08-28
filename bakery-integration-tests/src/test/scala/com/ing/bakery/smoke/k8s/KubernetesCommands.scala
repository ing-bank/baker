package com.ing.bakery.smoke.k8s

import cats.effect.IO

import scala.sys.process._

object KubernetesCommands {

  def exec(prefix: String, command: String): IO[Int] = {

    def processLogger(prefix: String): ProcessLogger = ProcessLogger(
      line => println(prefix + " " + line),
      err => stderr.println(Console.RED + err + Console.RESET))

    IO(command.!(processLogger(prefix)))
  }


}
