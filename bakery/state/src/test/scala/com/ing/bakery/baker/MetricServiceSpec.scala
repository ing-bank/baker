package com.ing.bakery.baker

import java.io.File
import java.net.InetSocketAddress
import cats.effect.IO
import com.ing.bakery.metrics.MetricService
import com.typesafe.config.ConfigFactory
import org.http4s.Status.Ok
import org.http4s.client.blaze.BlazeClientBuilder
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

import scala.concurrent.ExecutionContext
import cats.effect.Temporal

class MetricServiceSpec extends AnyFunSuite with Matchers {
  test("Metric service starts") {

    val configPath = sys.env.getOrElse("CONFIG_DIRECTORY", "/opt/docker/conf")
    val config = ConfigFactory.load(ConfigFactory.parseFile(new File(s"$configPath/application.conf")))
    val bakery = config.getConfig("baker")
    implicit val executionContext: ExecutionContext = ExecutionContext.global
    implicit val cs: ContextShift[IO] = IO.contextShift(executionContext)
    implicit val timer: Temporal[IO] = IO.timer(executionContext)
    val metricsPort = bakery.getInt("metrics-port")
    val mainResource  =
      for {
        metricsService <- MetricService.resource(
          InetSocketAddress.createUnresolved("0.0.0.0", metricsPort),
          executionContext
        )
        httpClient <- BlazeClientBuilder[IO](executionContext).resource
      } yield (metricsService, httpClient)

      mainResource use {
        case (_, client) =>
          client.get(s"http://localhost:$metricsPort") {
            case Ok(_) => IO.unit
            case _ =>  IO.raiseError(new IllegalStateException("Not started"))
          }
      } unsafeRunSync()

  }

}

