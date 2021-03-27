package com.ing.bakery.baker

import akka.actor.ActorSystem
import akka.http.scaladsl.model.HttpHeader.ParsingResult.Ok
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.typesafe.config.Config
import org.http4s.implicits._
import org.http4s.HttpRoutes
import org.http4s.Uri.RegName
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.server.blaze.BlazeServerBuilder
import org.http4s.server.{Router, Server}

import java.net.InetSocketAddress
import scala.concurrent.ExecutionContext
import org.http4s.dsl.io._

object ApiProxy {

  def resource(config: Config, system: ActorSystem, apiPort: Int)(implicit cs: ContextShift[IO], timer: Timer[IO], ec: ExecutionContext): Resource[IO, Server[IO]] = {

    val proxy = config.getString("baker.proxy.filter")
    val proxyPort = config.getInt("baker.proxy.port")
    lazy val unavailable = BlazeServerBuilder[IO](ec)
      .bindSocketAddress(InetSocketAddress.createUnresolved("0.0.0.0", proxyPort))
      .withHttpApp(
        Router("/" -> HttpRoutes.of[IO] {
          case _ => ServiceUnavailable()
        }) orNotFound).resource

    if (proxy != "") {
      Class.forName(proxy).getDeclaredConstructor().newInstance() match {
        case p: ProxyFilter =>
          val instance = p.instance(config, system)
          if (instance.enabled) {
            for {
              httpClient <- BlazeClientBuilder[IO](ec)
                .withCheckEndpointAuthentication(false)
                .resource
              server <- BlazeServerBuilder[IO](ec)
                .bindSocketAddress(InetSocketAddress.createUnresolved("0.0.0.0", p.port))
                .withHttpApp(
                  Router("/" -> HttpRoutes.of[IO] {
                    case req =>
                      val newAuthority = req.uri.authority.map(_.copy(host = RegName("localhost"), port = Some(apiPort)))
                      val proxiedReq = req.withUri(req.uri.copy(authority = newAuthority))
                      httpClient.run(proxiedReq).use(IO.pure)
                  }) orNotFound).resource
            } yield server
          } else unavailable
        case _ =>
          throw new IllegalArgumentException(s"Class $proxy defined in bakery.proxy-filter must extend com.ing.bakery.baker.ProxyFilter")
      }
    } else unavailable
  }
}

trait ProxyFilterInstance {
  def enabled: Boolean
}

trait ProxyFilter {
  def instance(config: Config, system: ActorSystem): ProxyFilterInstance
  def port: Int
}