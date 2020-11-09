package com.ing.bakery.baker

import java.io.CharArrayWriter
import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import io.prometheus.client.CollectorRegistry
import io.prometheus.client.exporter.common.TextFormat
import io.prometheus.client.hotspot._
import io.prometheus.jmx.JmxCollector
import kamon.KamonBridge
import org.http4s.dsl.io._
import org.http4s.implicits.http4sKleisliResponseSyntaxOptionT
import org.http4s.server.blaze.BlazeServerBuilder
import org.http4s.server.{Router, Server}
import org.http4s.{HttpRoutes, _}

import scala.concurrent.ExecutionContext
import scala.io.Source

object MetricService {

  def init: IO[Unit] = IO {
    standardCollectors.foreach(prometheusRegistry.register)
    KamonBridge.init()
  }

  def resource(socketAddress: InetSocketAddress)(implicit cs: ContextShift[IO], timer: Timer[IO], ec: ExecutionContext): Resource[IO, Server[IO]] = {
    val encoder = EntityEncoder.stringEncoder

    for {
      _ <- Resource.liftF(init)
      server <- BlazeServerBuilder[IO](ec)
        .bindSocketAddress(socketAddress)
        .withHttpApp(
          Router("/" ->
            HttpRoutes.of[IO] {
              case GET -> Root =>
                IO {
                  Response(
                    status = Ok,
                    body = encoder.toEntity(exportMetrics).body,
                    headers = Headers.of(Header("Content-Type", TextFormat.CONTENT_TYPE_004))
                  )
                }
            }
          ) orNotFound).resource
    } yield server
  }

  private lazy val prometheusRegistry: CollectorRegistry = CollectorRegistry.defaultRegistry

  private lazy val standardCollectors = Seq(
    new StandardExports,
    new MemoryPoolsExports(),
    new GarbageCollectorExports,
    new ThreadExports,
    new ClassLoadingExports,
    new VersionInfoExports,
    new JmxCollector(Source.fromResource("prometheus-jmx-collector.yaml").mkString)
  )

  def exportMetrics: String = {
    val writer = new CharArrayWriter(16 * 1024)
    TextFormat.write004(writer, prometheusRegistry.metricFamilySamples)
    writer.toString + "\n" + KamonBridge.prometheusFormatter.scrapeData()
  }

}
