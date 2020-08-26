package com.ing.bakery.interaction

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.bakery.protocol.{InteractionExecution => I}
import com.ing.baker.runtime.scaladsl.{IngredientInstance, InteractionInstance}
import org.http4s._
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.blaze._
import org.http4s.server.{Router, Server}

import scala.concurrent.ExecutionContext

object RemoteInteractionService {

  def resource(interactions: List[InteractionInstance], address: InetSocketAddress, tlsConfig: Option[BakeryHttp.TLSConfig])(implicit timer: Timer[IO], cs: ContextShift[IO]): Resource[IO, Server[IO]] = {
    val tls = tlsConfig.map { tlsConfig =>
      val sslConfig = BakeryHttp.loadSSLContext(tlsConfig)
      val sslParams = sslConfig.getDefaultSSLParameters
      sslParams.setNeedClientAuth(true)
      (sslConfig, sslParams)
    }
    val service = new RemoteInteractionService(interactions)
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

final class RemoteInteractionService(interactions: List[InteractionInstance])(implicit timer: Timer[IO], cs: ContextShift[IO]) {

  import com.ing.bakery.protocol.InteractionExecutionJsonCodecs._

  implicit val interactionEntityEncoder: EntityEncoder[IO, List[I.Interaction]] = jsonEncoderOf[IO,  List[I.Interaction]]

  implicit val executeRequestEntityDecoder: EntityDecoder[IO, List[IngredientInstance]] = jsonOf[IO, List[IngredientInstance]]
  implicit val executeResponseEntityEncoder: EntityEncoder[IO, I.ExecutionResult] = jsonEncoderOf[IO, I.ExecutionResult]

  def build: HttpApp[IO] =
    api.orNotFound

  private val Interactions = interactions.map(interaction =>
    I.Interaction(interaction.shaBase64, interaction.name, interaction.input.toList))

  def api: HttpRoutes[IO] = Router("/api/bakery" -> HttpRoutes.of[IO] {

    case GET -> Root / "health" => Ok("Ok")

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
  })
}
