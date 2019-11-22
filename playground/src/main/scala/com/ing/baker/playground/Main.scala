package com.ing.baker.playground

import cats.effect.{ExitCode, IO, IOApp}

object Main extends IOApp {

  override def run(args: List[String]): IO[ExitCode] = {
    PlaygroundApp.loop
      .run(AppUtils.Environment.empty)
      .map { case (finalState, _) =>
          println(s"Finishing with final state $finalState")
          ExitCode.Success
      }
  }
}
