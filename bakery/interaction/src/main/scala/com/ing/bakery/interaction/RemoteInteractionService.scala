package com.ing.bakery.interaction

import java.net.InetSocketAddress
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.bakery.protocol.{InteractionExecution => I}
import com.ing.baker.runtime.scaladsl.{IngredientInstance, InteractionInstance}
import com.ing.bakery.metrics.MetricService
import io.circe.Json
import io.circe.syntax._
import io.prometheus.client.CollectorRegistry
import org.http4s._
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.metrics.prometheus.Prometheus
import org.http4s.server.blaze._
import org.http4s.server.{Router, Server}
import org.http4s.server.middleware.{Logger, Metrics}

import scala.concurrent.ExecutionContext

object RemoteInteractionService {

  def resource(interactions: List[InteractionInstance],
               address: InetSocketAddress,
               tlsConfig: Option[BakeryHttp.TLSConfig],
               apiLoggingEnabled: Boolean = false,
               metricsPort: Int = 9096)(implicit timer: Timer[IO], cs: ContextShift[IO]): Resource[IO, Server[IO]] = {
    val tls = tlsConfig.map { tlsConfig =>
      val sslConfig = BakeryHttp.loadSSLContext(tlsConfig)
      val sslParams = sslConfig.getDefaultSSLParameters
      sslParams.setNeedClientAuth(true)
      (sslConfig, sslParams)
    }
    val service = new RemoteInteractionService(interactions)
    def interactionRequestClassifier(request: Request[IO]): Option[String] = {
      // ... /interactions/<id>/execute - we take ID part we care most about
      val p = request.pathInfo.split('/')
      if (p.length == 3) Some(p(2)) else None
    }

    for {
      metrics <- Prometheus.metricsOps[IO](CollectorRegistry.defaultRegistry, "http_interactions")
      app = BlazeServerBuilder[IO](ExecutionContext.global)
        .bindSocketAddress(address)
        .withHttpApp(
          Logger.httpApp(
            logHeaders = apiLoggingEnabled,
            logBody = apiLoggingEnabled,
            logAction = if (apiLoggingEnabled) Some( (x: String) => IO(println(x))) else None
          )(Router("/api/bakery" -> Metrics[IO](metrics,
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

final class RemoteInteractionService(interactions: List[InteractionInstance],
                                     apiLoggingEnabled: Boolean = false)(implicit timer: Timer[IO], cs: ContextShift[IO]) {

  import com.ing.bakery.protocol.InteractionExecutionJsonCodecs._

  implicit val interactionEntityEncoder: EntityEncoder[IO, List[I.Interaction]] = jsonEncoderOf[IO,  List[I.Interaction]]
  implicit val executeRequestEntityDecoder: EntityDecoder[IO, List[IngredientInstance]] = jsonOf[IO, List[IngredientInstance]]
  implicit val executeResponseEntityEncoder: EntityEncoder[IO, I.ExecutionResult] = jsonEncoderOf[IO, I.ExecutionResult]

  private val Interactions: List[I.Interaction] =
    interactions.map(interaction =>
      I.Interaction(interaction.shaBase64, interaction.name, interaction.input, interaction.output))

  def routes: HttpRoutes[IO] = HttpRoutes.of[IO] {

    case GET -> Root / "interactions" => Ok(Interactions)

    case req@POST -> Root /  "interactions" / id / "execute" =>
      for {
        request <- req.as[List[IngredientInstance]]
        response <- interactions.find(_.shaBase64 == id) match {
          case Some(interaction) =>
            IO.fromFuture(IO(interaction.run(request))).attempt.flatMap {
              case Right(value) =>
                Ok(I.ExecutionResult(Right(I.Success(value))))
              case Left(e) =>
                Ok(I.ExecutionResult(Left(I.Failure(I.InteractionError(e.getMessage)))))
            }
          case None =>
            Ok(I.ExecutionResult(Left(I.Failure(I.NoInstanceFound))))
        }
      } yield response
  }
}
