package com.ing.baker.baas.http

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.baas.server.BaasServer
import com.ing.baker.runtime.scaladsl.Baker
import com.typesafe.config.ConfigFactory

import scala.concurrent.Await
import scala.concurrent.duration._

object BaasApiStarter extends App {

  val host = "localhost"
  val port = 8081
  val actorSystem: ActorSystem = ActorSystem("baas-server") //TODO fix dependency injection
  val materializer: Materializer = ActorMaterializer.create(actorSystem)
  val baker = Baker.akka(ConfigFactory.load(), actorSystem, materializer)

  //Startup the BAAS cluster
  val baasAPI = new BaasServer(baker, host, port)(actorSystem)
  Await.result(baasAPI.start(), 10 seconds)
}
