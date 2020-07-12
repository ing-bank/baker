package com.ing.baker.baas.interaction

import java.net.InetSocketAddress

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.interaction.BakeryHttp.ProtoEntityEncoders._
import com.ing.baker.baas.protocol.InteractionSchedulingProto._
import com.ing.baker.baas.protocol.ProtocolInteractionExecution
import com.ing.baker.runtime.scaladsl.InteractionInstance
import org.http4s._
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

  def build: HttpApp[IO] =
    api.orNotFound

  def api: HttpRoutes[IO] = Router("/api/v3" -> HttpRoutes.of[IO] {

    case GET -> Root / "health" =>
      Ok("Ok")

    case GET -> Root / "interaction" =>
      Ok(ProtocolInteractionExecution.Interfaces(interactions.map(interaction =>
        ProtocolInteractionExecution.InstanceInterface(interaction.shaBase64, interaction.name, interaction.input))))

    case req@POST -> Root /  "interaction" / "apply" =>
      for {
        request <- req.as[ProtocolInteractionExecution.ExecuteInstance]
        response <- interactions.find(_.shaBase64 == request.id) match {
          case Some(interaction) =>
            IO.fromFuture(IO(interaction.run(request.input))).attempt.flatMap {
              case Right(value) =>
                Ok(ProtocolInteractionExecution.InstanceExecutedSuccessfully(value))
              case Left(e) =>
                Ok(ProtocolInteractionExecution.InstanceExecutionFailed(e.getMessage))
            }
          case None =>
            Ok(ProtocolInteractionExecution.NoInstanceFound)
        }
      } yield response
  })
}
