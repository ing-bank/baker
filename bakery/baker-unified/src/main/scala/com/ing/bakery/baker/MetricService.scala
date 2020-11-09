package com.ing.bakery.baker

import java.io.CharArrayWriter
import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import io.prometheus.client.exporter.common.TextFormat
import io.prometheus.client.hotspot._
import io.prometheus.client.{Collector, CollectorRegistry}
import kamon.Kamon
import org.http4s.HttpRoutes
import org.http4s.dsl.io._
import org.http4s.implicits.http4sKleisliResponseSyntaxOptionT
import org.http4s.server.{Router, Server}
import org.http4s.server.blaze.BlazeServerBuilder

import scala.concurrent.ExecutionContext

object MetricService {

  def addCollector(collector: Collector): Unit = prometheusRegistry.register(collector)

  def resource(socketAddress: InetSocketAddress)(implicit cs: ContextShift[IO], timer: Timer[IO], ec: ExecutionContext): Resource[IO, Server[IO]] = {
    standardCollectors.foreach(prometheusRegistry.register)
    Kamon.init()

    BlazeServerBuilder[IO](ec)
      .bindSocketAddress(socketAddress)
      .withHttpApp(
        Router("/app" ->
          HttpRoutes.of[IO] {
            case GET -> Root => Ok(exportMetrics)
          }
        ) orNotFound).resource
  }

  private lazy val prometheusRegistry: CollectorRegistry = CollectorRegistry.defaultRegistry

  private lazy val kamonPrometheusReporter = kamon.prometheus.PrometheusReporter.create()

  private lazy val standardCollectors = Seq(
    new StandardExports,
    new MemoryPoolsExports(),
    new GarbageCollectorExports,
    new ThreadExports,
    new ClassLoadingExports,
    new VersionInfoExports,
    // add custom jmx exports, if needed
    // new JmxCollector(Source.fromResource("jmx-collector.yaml"))
  )

  def exportMetrics: IO[String] = IO {
    val writer = new CharArrayWriter(16 * 1024)
    TextFormat.write004(writer, prometheusRegistry.metricFamilySamples)
    writer.toString + "\n" + kamonPrometheusReporter.scrapeData()
  }

}
