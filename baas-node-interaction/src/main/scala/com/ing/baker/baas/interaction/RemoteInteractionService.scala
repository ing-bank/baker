package com.ing.baker.baas.interaction

import java.io.InputStream
import java.net.InetSocketAddress
import java.security.{KeyStore, SecureRandom}

import javax.net.ssl.{KeyManagerFactory, SSLContext, SSLParameters, TrustManagerFactory}
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.baas.interaction.BakeryHttp.ProtoEntityEncoders._
import com.ing.baker.baas.protocol.InteractionSchedulingProto._
import com.ing.baker.baas.protocol.ProtocolInteractionExecution
import com.ing.baker.runtime.scaladsl.InteractionInstance
import org.http4s._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.blaze.BlazeServerBuilder
import org.http4s.server.{Router, Server}

object RemoteInteractionService {

  case class TLSConfig(password: String, keystorePath: String)

  def loadSSLContext(config: TLSConfig): (SSLContext, SSLParameters) = {
    val password: Array[Char] = config.password.toCharArray

    val ks: KeyStore = KeyStore.getInstance("JKS")
    val keystore: InputStream = getClass.getClassLoader.getResourceAsStream(config.keystorePath)

    require(keystore != null, "Keystore required!")
    ks.load(keystore, password)

    val keyManagerFactory: KeyManagerFactory = KeyManagerFactory.getInstance("SunX509")
    keyManagerFactory.init(ks, password)

    val tmf: TrustManagerFactory = TrustManagerFactory.getInstance("SunX509")
    tmf.init(ks)

    val sslContext: SSLContext = SSLContext.getInstance("TLS")
    sslContext.init(keyManagerFactory.getKeyManagers, tmf.getTrustManagers, new SecureRandom)

    val params: SSLParameters = sslContext.getDefaultSSLParameters
    params.setNeedClientAuth(true)
    (sslContext, params)
  }

  def resource(interactions: List[InteractionInstance], address: InetSocketAddress, tlsConfig: TLSConfig)(implicit timer: Timer[IO], cs: ContextShift[IO]): Resource[IO, Server[IO]] = {
    val (sslConfig, sslParams) = loadSSLContext(tlsConfig)
    BlazeServerBuilder[IO]
      .bindSocketAddress(address)
      .withSslContextAndParameters(sslConfig, sslParams)
      .withHttpApp(new RemoteInteractionService(interactions).build)
      .resource
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
