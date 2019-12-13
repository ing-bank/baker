package com.ing.baker.baas.state

import akka.actor.ActorSystem
import akka.stream.ActorMaterializer
import com.ing.baker.runtime.akka.AkkaBaker
import com.typesafe.config.ConfigFactory

import scala.concurrent.Await
import scala.concurrent.duration._

object Main extends App {
  private val timeout: FiniteDuration = 20.seconds

  println(Console.YELLOW + "Starting State Node..." + Console.RESET)

  val config = ConfigFactory.load()
  val systemName = config.getString("service.actorSystemName")
  val httpServerPort = config.getInt("service.httpServerPort")
  val stateNodeSystem = ActorSystem(systemName)
  val stateNodeBaker = AkkaBaker(config, stateNodeSystem)
  val materializer = ActorMaterializer()(stateNodeSystem)

  import stateNodeSystem.dispatcher

  Await.result(BaaSServer.run(stateNodeBaker, "0.0.0.0", httpServerPort)(stateNodeSystem, materializer).map { hook =>
    println(Console.GREEN + "State Node started..." + Console.RESET)
    println(hook.localAddress)
    sys.addShutdownHook(Await.result(hook.unbind(), timeout))
  }, timeout)
}
