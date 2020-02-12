package com.ing.baker.baas.dashboard

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.baas.akka.DashboardHttp
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.ConfigFactory

import scala.concurrent.Await
import scala.concurrent.duration._

object Main extends App {

  val config = ConfigFactory.load()

  val dashboardPort = config.getString("bakery-component.dashboard-port").toInt
  val bakerEventListenerPort = config.getString("bakery-component.baker-event-listener-port").toInt
  val stateNodeHostname = config.getString("bakery.state-node-hostname")

  implicit val system: ActorSystem = ActorSystem("RemoteEventListenerSystem", config)
  implicit val materializer: Materializer = ActorMaterializer()
  implicit val encryption: Encryption = Encryption.from(config)

  import system.dispatcher

  for {
    bakeryApi <- BakeryApi.runWith(stateNodeHostname, bakerEventListenerPort).unsafeToFuture()
    _ <- DashboardHttp.run(bakeryApi)( "0.0.0.0", dashboardPort).map { hook =>
      sys.addShutdownHook(Await.result(hook.unbind(), 20.seconds))
    }
  } yield ()
}
