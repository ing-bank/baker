package com.ing.baker.baas.http

import akka.actor.ActorSystem
import com.ing.baker.baas.server.BaasServer
import com.ing.baker.runtime.scaladsl.Baker

import scala.concurrent.Await
import scala.concurrent.duration._

object BaasApiStarter extends App {

  val host = "localhost"
  val port = 8081
  implicit val actorSystem: ActorSystem = ActorSystem("baas-server") //TODO fix dependency injection
  val baker = Baker.akka(actorSystem)

  //Startup the BAAS cluster
  val baasAPI = new BaasServer(baker, host, port)
  Await.result(baasAPI.start(), 10 seconds)
}
