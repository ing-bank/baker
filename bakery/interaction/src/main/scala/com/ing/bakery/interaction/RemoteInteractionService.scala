package com.ing.bakery.interaction

import java.net.{InetSocketAddress, URLEncoder}
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.scaladsl.{IngredientInstance, InteractionInstance}
import com.ing.baker.runtime.serialization.InteractionExecution.Interactions
import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs.interactionsCodec
import com.ing.baker.runtime.serialization.{InteractionExecution => I}
import com.ing.bakery.metrics.MetricService
import com.typesafe.scalalogging.LazyLogging
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
import io.circe.parser._

import java.lang.reflect.InvocationTargetException
import scala.concurrent.{ExecutionContext, Future}
import com.ing.baker.runtime.serialization.InteractionExecutionJsonCodecs._
import com.ing.baker.runtime.serialization.JsonCodec._
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.ing.baker.runtime.serialization.JsonDecoders._
import io.circe.generic.semiauto.{deriveDecoder, deriveEncoder}

import java.util.concurrent.CompletableFuture
import scala.collection.JavaConverters
import scala.compat.java8.FutureConverters._

object RemoteInteractionService {

  def resource(interactions: List[InteractionInstance],
               address: InetSocketAddress,
               tlsConfig: Option[BakeryHttp.TLSConfig],
               apiLoggingEnabled: Boolean = false,
               interactionPerTypeMetricsEnabled: Boolean = true,
               metricsPort: Int = 9096,
               metricsEnabled: Boolean = false,
               apiUrlPrefix: String = "/api/bakery/interactions")(implicit timer: Timer[IO], cs: ContextShift[IO], executionContext: ExecutionContext): Resource[IO, Server[IO]] = {

    val idToNameMap = interactions.map(i => URLEncoder.encode(i.shaBase64, "UTF-8").take(8) -> i.name).toMap

    val tls = tlsConfig.map { tlsConfig =>
      val sslConfig = BakeryHttp.loadSSLContext(tlsConfig)
      val sslParams = sslConfig.getDefaultSSLParameters
      sslParams.setNeedClientAuth(true)
      (sslConfig, sslParams)
    }
    val service = new RemoteInteractionService(interactions)

    def interactionRequestClassifier(request: Request[IO]): Option[String] = if (interactionPerTypeMetricsEnabled) {
      val p = request.pathInfo.split('/') // ... /interactions/<id>/execute - we take ID part we care most about
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
            logAction = if (apiLoggingEnabled) Some((x: String) => IO(println(x))) else None
          )(Router(apiUrlPrefix -> Metrics[IO](metrics,
            classifierF = interactionRequestClassifier)(service.routes)) orNotFound)
        )
      server <- (tls match {
        case Some((sslConfig, sslParams)) => app.withSslContextAndParameters(sslConfig, sslParams)
        case None => app
      }).resource
      _ <- if (metricsEnabled)
        MetricService.resource(InetSocketAddress.createUnresolved("0.0.0.0", metricsPort)
        )(cs, timer, ExecutionContext.global) else Resource.eval(IO.unit)

    } yield server

  }
}

abstract class InteractionExecutor extends LazyLogging {

  def interactions: List[InteractionInstance]
  def executionContext: ExecutionContext
  implicit val contextShift: ContextShift[IO] = IO.contextShift(executionContext)
  implicit val timer: Timer[IO] = IO.timer(executionContext)

  protected val CurrentInteractions: Interactions =
    Interactions(System.currentTimeMillis,
      interactions.map(interaction =>
        I.Descriptor(interaction.shaBase64, interaction.name, interaction.input, interaction.output))
    )

  protected def executionFailure(interactionName: String, message: String): IO[I.ExecutionResult] = IO(I.ExecutionResult(
    Left(I.Failure(I.InteractionError(
      interactionName = interactionName,
      message = Option(message).getOrElse("NullPointerException"))
    ))))


  protected def execute(id: String, request: List[IngredientInstance]): IO[I.ExecutionResult] = {
    interactions.find(_.shaBase64 == id) match {
      case Some(interaction) =>
        IO.fromFuture(IO(interaction.run(request))).attempt.flatMap {
          case Right(value) => IO(I.ExecutionResult(Right(I.Success(value))))
          case Left(e) =>
            val rootCause = e match {
              case _: InvocationTargetException if Option(e.getCause).isDefined => e.getCause
              case _ => e
            }
            logger.error(s"Interaction ${interaction.name} failed with an exception: ${rootCause.getMessage}", rootCause)
            executionFailure(interaction.name, rootCause.getMessage)
        }
      case None => IO(I.ExecutionResult(Left(I.Failure(I.NoInstanceFound))))
    }
  }
}

class InteractionExecutorJava(implementations: java.util.List[InteractionInstance],
                              val executionContext: ExecutionContext)
  extends InteractionExecutor {
  private lazy val javaInteractions = JavaConverters.collectionAsScalaIterable(implementations).toList
  def interactions: List[InteractionInstance] = javaInteractions

  def list: String = interactionsCodec(CurrentInteractions).noSpaces

  def run(id: String, ingredientsJson: String): CompletableFuture[String] = ((for {
    json <- parse(ingredientsJson)
    ingredients <- json.as[List[IngredientInstance]]
  } yield {
    execute(id, ingredients)
  }) match {
    case Right(result) => result
    case Left(error) => executionFailure(id, error.getMessage)
  }).map(executionResultEncoder.apply)
    .map(_.noSpaces)
    .unsafeToFuture().toJava.toCompletableFuture
}

final class RemoteInteractionService(val interactions: List[InteractionInstance])(implicit val executionContext: ExecutionContext)
  extends InteractionExecutor {

  implicit val interactionEntityEncoder: EntityEncoder[IO, Interactions] = jsonEncoderOf[IO, Interactions]
  implicit val executeRequestEntityDecoder: EntityDecoder[IO, List[IngredientInstance]] = jsonOf[IO, List[IngredientInstance]]
  implicit val executeResponseEntityEncoder: EntityEncoder[IO, I.ExecutionResult] = jsonEncoderOf[IO, I.ExecutionResult]

  def routes: HttpRoutes[IO] = HttpRoutes.of[IO] {

    case GET -> Root => Ok(CurrentInteractions)

    case req@POST -> Root / id / "execute" =>
      for {
        ingredients <- req.as[List[IngredientInstance]]
        result <- execute(id, ingredients)
        response <- Ok(result)
      } yield response
  }

}
