package com.ing.bakery.baker

import java.io.File
import java.net.InetSocketAddress

import akka.actor.ActorSystem
import cats.effect.{ContextShift, ExitCode, IO, Resource, Timer}
import com.typesafe.config.ConfigFactory
import org.http4s.server.Server
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

import scala.concurrent.ExecutionContext

class MetricServiceSpec extends AnyFunSuite with Matchers {

  test("Metric service starts") {

// todo fix
//    val configPath = sys.env.getOrElse("CONFIG_DIRECTORY", "/opt/docker/conf")
//    val config = ConfigFactory.load(ConfigFactory.parseFile(new File(s"$configPath/application.conf")))
//    val bakery = config.getConfig("bakery")
//    implicit val executionContext: ExecutionContext = ExecutionContext.global
//    implicit val cs: ContextShift[IO] = IO.contextShift(executionContext)
//    implicit val timer: Timer[IO] = IO.timer(executionContext)
//    val metricsPort = bakery.getInt("metrics-port")
//    val mainResource: Resource[IO, Server[IO]] =
//      for {
//        metricsService <- MetricService.resource(
//          InetSocketAddress.createUnresolved("0.0.0.0", metricsPort)
//        )
//      } yield metricsService
//
//    mainResource.use( _ => { IO.never }).unsafeRunSync()
//

  }

}

