package com.ing.baker.baas.http

import akka.actor.ActorSystem
import com.ing.baker.baas.{BAAS, BAASClient}
import com.ing.baker.baas.BAASSpec.InteractionOne

import scala.concurrent.Await
import scala.concurrent.duration._

object BAASAPIRunner extends App {
  //Startup the BAASAPI
  val baasAPI = new BAASAPI(new BAAS())(ActorSystem("BAASAPIActorSystem"))
  Await.result(baasAPI.start(), 10 seconds)

  //Add the implementation to the BAASAPI
  val baasClient: BAASClient = new BAASClient("http://localhost", 8081)
  baasClient.addImplementation(InteractionOne())
}

class BAASAPIRunner {

}
