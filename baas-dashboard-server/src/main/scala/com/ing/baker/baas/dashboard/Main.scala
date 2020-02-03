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

  /*
  val config: Config = ConfigFactory.parseString(
    """
      |include "baker.conf"
      |
      |akka {
      |  persistence.journal.plugin = "inmemory-journal"
      |  persistence.snapshot-store.plugin = "inmemory-snapshot-store"
      |}
      |
      |inmemory-read-journal {
      |  write-plugin = "inmemory-journal"
      |  offset-mode = "sequence"
      |  ask-timeout = "10s"
      |  refresh-interval = "50ms"
      |  max-buffer-size = "100"
      |}
      |
      |akka {
      |  actor {
      |    provider = "cluster"
      |  }
      |  remote {
      |    log-remote-lifecycle-events = off
      |    netty.tcp {
      |      hostname = "127.0.0.1"
      |      port = 2555
      |    }
      |  }
      |
      |  cluster {
      |    seed-nodes = ["akka.tcp://RemoteEventListenerSystem@127.0.0.1:2555"]
      |    auto-down-unreachable-after = 10s
      |  }
      |}
        """.stripMargin).withFallback(ConfigFactory.load())
   */
  val config = ConfigFactory.load()

  val port = config.getInt("baas-component.http-api-port")
  val baasHostname = config.getString("baas.state-node-hostname")

  implicit val system: ActorSystem = ActorSystem("RemoteEventListenerSystem", config)
  implicit val materializer: Materializer = ActorMaterializer()
  // TODO load correct encryption from config
  implicit val encryption: Encryption = Encryption.NoEncryption
  import system.dispatcher

  val baker = BakerClient(Uri.parseAbsolute(baasHostname))

  println(Console.GREEN + "Will start server" + Console.RESET)

  DashboardHttp.run(baker)( "0.0.0.0", port).foreach { hook =>
    println(Console.GREEN + "Http server started" + Console.RESET)
    println(hook.localAddress)
    sys.addShutdownHook(Await.result(hook.unbind(), 20.seconds))
  }
}
