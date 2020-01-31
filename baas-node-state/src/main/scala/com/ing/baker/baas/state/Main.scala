package com.ing.baker.baas.state

import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.stream.ActorMaterializer
import com.ing.baker.runtime.akka.AkkaBaker
import com.typesafe.config.ConfigFactory

import scala.concurrent.Await
import scala.concurrent.duration._

object Main extends App {
  private val timeout: FiniteDuration = 20.seconds

  println(Console.YELLOW + "Starting State Node..." + Console.RESET)

  val config = ConfigFactory.load()
  val httpServerPort = config.getInt("baas-component.http-api-port")
  val stateNodeSystem = ActorSystem("BaaSStateNodeSystem")
  val stateNodeBaker = AkkaBaker(config, stateNodeSystem)
  val materializer = ActorMaterializer()(stateNodeSystem)

  import stateNodeSystem.dispatcher

  Cluster(stateNodeSystem).registerOnMemberUp {

    println(Console.YELLOW + httpServerPort + Console.RESET)

    BaaSServer.run(stateNodeBaker, "0.0.0.0", httpServerPort)(stateNodeSystem, materializer).foreach { hook =>
      println(Console.GREEN + "State Node started..." + Console.RESET)
      sys.addShutdownHook(Await.result(hook.unbind(), timeout))
    }
  }

}
