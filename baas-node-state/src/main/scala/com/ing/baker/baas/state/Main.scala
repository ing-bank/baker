package com.ing.baker.baas.state

import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.baas.listeners.EventListenersKubernetes
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.ConfigFactory

import scala.concurrent.Await
import scala.concurrent.duration._

object Main extends App {
  private val timeout: FiniteDuration = 20.seconds

  println(Console.YELLOW + "Starting State Node..." + Console.RESET)

  val config = ConfigFactory.load()

  val httpServerPort = config.getInt("baas-component.http-api-port")
  val kubeNamespace = config.getString("baker.interaction-manager.kube-namespace")

  implicit val stateNodeSystem = ActorSystem("BaaSStateNodeSystem")
  implicit val materializer: Materializer = ActorMaterializer()
  // TODO get this from config
  implicit val encryption: Encryption = Encryption.NoEncryption

  val stateNodeBaker = AkkaBaker(config, stateNodeSystem)
  val kube = new KubernetesFunctions(kubeNamespace)
  val listeners = new EventListenersKubernetes(kube, stateNodeBaker)

  import stateNodeSystem.dispatcher

  Cluster(stateNodeSystem).registerOnMemberUp {

    println(Console.YELLOW + httpServerPort + Console.RESET)

    BaaSServer.run(listeners, stateNodeBaker, "0.0.0.0", httpServerPort).foreach { hook =>
      println(Console.GREEN + "State Node started..." + Console.RESET)
      sys.addShutdownHook(Await.result(hook.unbind(), timeout))
    }
  }

}
