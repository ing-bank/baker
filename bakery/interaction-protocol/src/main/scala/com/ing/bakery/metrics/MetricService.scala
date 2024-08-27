package com.ing.bakery.metrics

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.typesafe.scalalogging.LazyLogging
import io.prometheus.client.exporter.common.TextFormat
import io.prometheus.client.hotspot._
import io.prometheus.client.{Collector, CollectorRegistry, Counter}
import io.prometheus.jmx.JmxCollector
import org.http4s.dsl.io._
import org.http4s.implicits.http4sKleisliResponseSyntaxOptionT
import org.http4s.server.blaze.BlazeServerBuilder
import org.http4s.server.{Router, Server}
import org.http4s._

import java.io.CharArrayWriter
import java.net.InetSocketAddress
import scala.concurrent.ExecutionContext
import scala.io.Source

class MetricService(val registry: CollectorRegistry) extends LazyLogging {
  try {
    DefaultExports.register(registry)
    registry.register(new JmxCollector(Source.fromResource("prometheus-jmx-collector.yaml").mkString))
  } catch {
    case e: Exception =>
      logger.error(s"No prometheus-jmx-collector.yaml found in classpath, JMX export is not enabled: ${e.getMessage}")
  }

  val interactionSuccessCounter: Counter = counter("bakery_interaction_success", "Successful interaction calls")
  val interactionFailureCounter: Counter = counter("bakery_interaction_failure", "Failed interaction calls")

  def counter(name: String, help: String): Counter = {
    Counter
      .build()
      .name(name)
      .help(help)
      .create()
      .register(registry)
  }

  def register(collector: Collector): Unit = registry.register(collector)
}

object MetricService extends LazyLogging {

  def defaultInstance = new MetricService(new CollectorRegistry(true))

  def resourceServer(socketAddress: InetSocketAddress, registry: CollectorRegistry, ec: ExecutionContext)
                    (implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Server[IO]] = {
    val encoder = EntityEncoder.stringEncoder

    def fromPrometheus: String = {
      val writer = new CharArrayWriter(16 * 1024)
      TextFormat.write004(writer, registry.metricFamilySamples)
      writer.toString
    }

    def exportMetrics: String = fromPrometheus

    for {
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
}