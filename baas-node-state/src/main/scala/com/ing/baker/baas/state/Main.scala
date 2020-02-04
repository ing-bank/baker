package com.ing.baker.baas.state

import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.ConfigFactory

import scala.concurrent.Await
import scala.concurrent.duration._

object Main extends App {

  // Config
  val config = ConfigFactory.load()
  val httpServerPort = config.getInt("baas-component.http-api-port")
  val namespace = config.getString("baas-component.kubernetes-namespace")

  // Core dependencies
  implicit val system: ActorSystem = ActorSystem("BaaSStateNodeSystem")
  implicit val materializer: Materializer = ActorMaterializer()
  implicit val encryption: Encryption = Encryption.from(config)

  // Dependencies
  val kubernetes = new ServiceDiscoveryKubernetes(namespace)
  val interactionManager = new InteractionsServiceDiscovery(kubernetes)
  val stateNodeBaker = AkkaBaker.withConfig(AkkaBakerConfig(
    interactionManager = interactionManager,
    bakerActorProvider = AkkaBakerConfig.bakerProviderFrom(config),
    readJournal = AkkaBakerConfig.persistenceQueryFrom(config, system),
    timeouts = AkkaBakerConfig.Timeouts.from(config)
  )(system))
  val eventListeners = new EventListenersServiceDiscovery(kubernetes, stateNodeBaker)

  import system.dispatcher

  // Server init
  Cluster(system).registerOnMemberUp {
    BaaSServer.run(eventListeners, stateNodeBaker, "0.0.0.0", httpServerPort).foreach { hook =>
      sys.addShutdownHook(Await.result(hook.unbind(), 20.seconds))
    }
  }

}
