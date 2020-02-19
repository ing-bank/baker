package com.ing.baker.baas.dashboard

import java.net.InetSocketAddress

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.IO
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.Config

case class DashboardDependencies(
  stateNodeAddress: InetSocketAddress,
  eventListenerAddress: InetSocketAddress,
  dashboardServiceAddress: InetSocketAddress,
  _system: ActorSystem,
  _materializer: Materializer,
  _encryption: Encryption
) {

  implicit val system: ActorSystem = _system

  implicit val materializer: Materializer = _materializer

  implicit val encryption: Encryption = _encryption
}

object DashboardDependencies {

  def from(config: Config): IO[DashboardDependencies] = IO {
    val dashboardPort = config.getString("bakery-component.dashboard-port").toInt
    val bakerEventListenerPort = config.getString("bakery-component.baker-event-listener-port").toInt
    val stateNodeHostname = config.getString("bakery.state-node-hostname")
    val stateNodeHostSplit = stateNodeHostname.split(":")

    val system: ActorSystem = ActorSystem("RemoteEventListenerSystem", config)
    val materializer: Materializer = ActorMaterializer()(system)
    val encryption: Encryption = Encryption.from(config)

    DashboardDependencies(
      stateNodeAddress = InetSocketAddress
        .createUnresolved(stateNodeHostSplit(0), stateNodeHostSplit(1).toInt),
      eventListenerAddress = InetSocketAddress
        .createUnresolved("0.0.0.0", bakerEventListenerPort),
      dashboardServiceAddress = InetSocketAddress
        .createUnresolved("0.0.0.0", dashboardPort),
      _system = system,
      _materializer = materializer,
      _encryption = encryption
    )
  }
}

