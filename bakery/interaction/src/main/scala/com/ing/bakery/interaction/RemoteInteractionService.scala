package com.ing.bakery.interaction

import java.net.{InetSocketAddress, URLEncoder}
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.scaladsl.{IngredientInstance, InteractionInstance}
import com.ing.baker.runtime.serialization.{InteractionExecution => I}
import com.ing.bakery.metrics.MetricService
import com.typesafe.scalalogging.LazyLogging
import io.circe.Json
import io.circe.syntax._
import io.prometheus.client.CollectorRegistry
import org.http4s._
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.metrics.prometheus.Prometheus
import org.http4s.blaze.server._
import org.http4s.server.{Router, Server}
import org.http4s.server.middleware.{Logger, Metrics}

import java.lang.reflect.InvocationTargetException
import scala.concurrent.ExecutionContext

object RemoteInteractionService {

  def resource(interactions: List[InteractionInstance],
               address: InetSocketAddress,
               tlsConfig: Option[BakeryHttp.TLSConfig],
               apiLoggingEnabled: Boolean = false,
               interactionPerTypeMetricsEnabled: Boolean = true,
               metricsPort: Int = 9096,
               apiUrlPrefix: String = "/api/bakery/interactions")(implicit timer: Timer[IO], cs: ContextShift[IO]): Resource[IO, Server[IO]] = {

    val idToNameMap = interactions.map(i => URLEncoder.encode(i.shaBase64, "UTF-8").take(8) -> i.name ).toMap

    val tls = tlsConfig.map { tlsConfig =>
      val sslConfig = BakeryHttp.loadSSLContext(tlsConfig)
      val sslParams = sslConfig.getDefaultSSLParameters
      sslParams.setNeedClientAuth(true)
      (sslConfig, sslParams)
    }
    val service = new RemoteInteractionService(interactions)

    def interactionRequestClassifier(request: Request[IO]): Option[String] = if (interactionPerTypeMetricsEnabled) {
      val p = request.pathInfo.split('/')       // ... /interactions/<id>/execute - we take ID part we care most about
      (if (p.length == 4) Some(p(2)) else None).map(v => idToNameMap.getOrElse(v.take(8), "unknown"))
    } else None

    for {
      metrics <- Prometheus.metricsOps[IO](CollectorRegistry.defaultRegistry, "http_interactions")
      app = BlazeServerBuilder[IO](ExecutionContext.global)
        .bindSocketAddress(address)
        .withHttpApp(
          Logger.httpApp(
            logHeaders = apiLoggingEnabled,
            logBody = apiLoggingEnabled,
            logAction = if (apiLoggingEnabled) Some( (x: String) => IO(println(x))) else None
          )(Router(apiUrlPrefix -> Metrics[IO](metrics,
            classifierF = interactionRequestClassifier)(service.routes)) orNotFound)
        )
      server <- (tls match {
        case Some((sslConfig, sslParams)) => app.withSslContextAndParameters(sslConfig, sslParams)
        case None => app
      }).resource
      _ <- MetricService.resource(
        InetSocketAddress.createUnresolved("0.0.0.0", metricsPort)
      )(cs, timer, ExecutionContext.global)

    } yield server

  }
}

final class RemoteInteractionService(interactions: List[InteractionInstance])(implicit timer: Timer[IO], cs: ContextShift[IO]) extends LazyLogging {

  import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs._
  import com.ing.baker.runtime.serialization.JsonCodec._

  implicit val interactionEntityEncoder: EntityEncoder[IO, List[I.Descriptor]] = jsonEncoderOf[IO,  List[I.Descriptor]]
  implicit val executeRequestEntityDecoder: EntityDecoder[IO, List[IngredientInstance]] = jsonOf[IO, List[IngredientInstance]]
  implicit val executeResponseEntityEncoder: EntityEncoder[IO, I.ExecutionResult] = jsonEncoderOf[IO, I.ExecutionResult]

  private val Interactions: List[I.Descriptor] =
    interactions.map(interaction =>
      I.Descriptor(interaction.shaBase64, interaction.name, interaction.input, interaction.output))

  def routes: HttpRoutes[IO] = HttpRoutes.of[IO] {

    case GET -> Root => Ok(Interactions)

    case req@POST -> Root / id / "execute" =>
      for {
        request <- req.as[List[IngredientInstance]]
        response <- interactions.find(_.shaBase64 == id) match {
          case Some(interaction) =>
            IO.fromFuture(IO(interaction.run(request))).attempt.flatMap {
              case Right(value) =>
                Ok(I.ExecutionResult(Right(I.Success(value))))
              case Left(e) =>
                val rootCause = e match {
                  case _: InvocationTargetException if Option(e.getCause).isDefined => e.getCause
                  case _ => e
                }
                logger.error(s"Interaction ${interaction.name} failed with an exception: ${rootCause.getMessage}", rootCause)
                Ok(I.ExecutionResult(
                  Left(I.Failure(I.InteractionError(
                    interactionName = interaction.name,
                    message = Option(rootCause.getMessage).getOrElse("NullPointerException"))
                  ))))
            }
          case None =>
            Ok(I.ExecutionResult(Left(I.Failure(I.NoInstanceFound))))
        }
      } yield response
  }
}
