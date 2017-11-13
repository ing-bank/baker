package com.ing.baker.baas.http

import akka.actor.ActorSystem
import com.ing.baker.baas.BAAS

import scala.concurrent.Await
import scala.concurrent.duration._

object BAASAPIRunner extends App {

  val host = "localhost"
  val port = 8081
  val actorSystem = ActorSystem("BAASAPIActorSystem")
  val baas = new BAAS(actorSystem)

  //Startup the BAASAPI
  val baasAPI = new BAASAPI(baas, host, port)(actorSystem)
  Await.result(baasAPI.start(), 10 seconds)
}
