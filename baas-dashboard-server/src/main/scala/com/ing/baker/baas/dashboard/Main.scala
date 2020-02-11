package com.ing.baker.baas.dashboard

import akka.actor.ActorSystem
import akka.http.scaladsl.model.Uri
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.baas.akka.DashboardHttp
import com.ing.baker.baas.scaladsl.BakerClient
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.ConfigFactory

import scala.concurrent.Await
import scala.concurrent.duration._

object Main extends App {

  val config = ConfigFactory.load()

  val port = config.getInt("baas-component.http-api-port")
  val bakerEventListenerPort = config.getString("baas-component.baker-event-listener-port")
  val stateNodeHostname = config.getString("baas.state-node-hostname")

  implicit val system: ActorSystem = ActorSystem("RemoteEventListenerSystem", config)
  implicit val materializer: Materializer = ActorMaterializer()
  // TODO load correct encryption from config
  implicit val encryption: Encryption = Encryption.NoEncryption
  import system.dispatcher

  val baker = BakerClient(Uri.parseAbsolute(stateNodeHostname))

  DashboardHttp.run(baker)( "0.0.0.0", port).foreach { hook =>
    sys.addShutdownHook(Await.result(hook.unbind(), 20.seconds))
  }
}
