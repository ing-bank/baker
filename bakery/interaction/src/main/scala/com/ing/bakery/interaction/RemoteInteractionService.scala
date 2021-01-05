package com.ing.bakery.interaction

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.bakery.protocol.{InteractionExecution => I}
import com.ing.baker.runtime.scaladsl.{IngredientInstance, InteractionInstance}
import io.circe.Json
import io.circe.syntax._
import org.http4s._
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.blaze._
import org.http4s.server.{Router, Server}
import org.http4s.server.middleware.Logger

import scala.concurrent.ExecutionContext

object RemoteInteractionService {

  def resource(interactions: List[InteractionInstance],
               address: InetSocketAddress,
               tlsConfig: Option[BakeryHttp.TLSConfig],
               apiLoggingEnabled: Boolean = false)(implicit timer: Timer[IO], cs: ContextShift[IO]): Resource[IO, Server[IO]] = {
    val tls = tlsConfig.map { tlsConfig =>
      val sslConfig = BakeryHttp.loadSSLContext(tlsConfig)
      val sslParams = sslConfig.getDefaultSSLParameters
      sslParams.setNeedClientAuth(true)
      (sslConfig, sslParams)
    }
    val service = new RemoteInteractionService(interactions, apiLoggingEnabled)
    val builder0 = BlazeServerBuilder[IO](ExecutionContext.global)
      .bindSocketAddress(address)
      .withHttpApp(service.build)
    val builder1 = tls match {
      case Some((sslConfig, sslParams)) => builder0.withSslContextAndParameters(sslConfig, sslParams)
      case None => builder0
    }
    builder1.resource
  }
}

final class RemoteInteractionService(interactions: List[InteractionInstance],
                                     apiLoggingEnabled: Boolean = false)(implicit timer: Timer[IO], cs: ContextShift[IO]) {

  import com.ing.bakery.protocol.InteractionExecutionJsonCodecs._

  implicit val interactionEntityEncoder: EntityEncoder[IO, List[I.Interaction]] = jsonEncoderOf[IO,  List[I.Interaction]]
  implicit val executeRequestEntityDecoder: EntityDecoder[IO, List[IngredientInstance]] = jsonOf[IO, List[IngredientInstance]]
  implicit val executeResponseEntityEncoder: EntityEncoder[IO, I.ExecutionResult] = jsonEncoderOf[IO, I.ExecutionResult]

  def build: HttpApp[IO] = Logger.httpApp(
    logHeaders = apiLoggingEnabled,
    logBody = apiLoggingEnabled,
    logAction = if (apiLoggingEnabled) Some( (x: String) => IO(println(x))) else None,
  )(api.orNotFound)

  private val Interactions: List[I.Interaction] =
    interactions.map(interaction =>
      I.Interaction(interaction.shaBase64, interaction.name, interaction.input.toList))

  def api: HttpRoutes[IO] = Router("/api/bakery" -> HttpRoutes.of[IO] {

    case GET -> Root / "interactions" => Ok(Interactions)

    case GET -> Root / "interactions-with-version" =>
      // Environment variable injected by the Bakery Controller from the Interaction Resource Definition file
      val version: String = sys.env.getOrElse("BAKERY_INTERACTION_VERSION", "unknown")
      Ok(Json.obj(
        "version" -> Json.fromString(version),
        "interactions" -> Json.fromValues(Interactions.map(_.asJson))
      ))

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
  })
}
