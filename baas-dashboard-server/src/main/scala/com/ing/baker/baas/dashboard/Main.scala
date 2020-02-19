package com.ing.baker.baas.dashboard

import cats.effect.{ExitCode, IO, IOApp}
import cats.implicits._
import com.typesafe.config.ConfigFactory

object Main extends IOApp {

  override def run(args: List[String]): IO[ExitCode] =
    for {
      dependencies <- DashboardDependencies.from(ConfigFactory.load())
      exitCode <- DashboardService
        .resource(dependencies)
        .use(_ => IO.never)
        .as(ExitCode.Success)
    } yield exitCode
}
