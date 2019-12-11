package com.ing.baker.playground

import cats.effect.{ExitCode, IO, IOApp}
import com.typesafe.scalalogging.LazyLogging

object Main extends IOApp with LazyLogging {

  override def run(args: List[String]): IO[ExitCode] = {
    PlaygroundApp.loop
      .run(AppUtils.Environment.empty)
      .map { case (finalState, _) =>
        logger.info(s"Finishing with final state $finalState")
        ExitCode.Success
      }
  }
}
