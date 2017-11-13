package com.ing.baker.baas.http

import akka.actor.ActorSystem
import com.ing.baker.baas.BAASSpec.InteractionOne
import com.ing.baker.baas.{BAAS, BAASClient}

object ImplementationRunner extends App {

  val host = "localhost"
  val port = 8081
  val actorSystem = ActorSystem("ImplementatieRunner")
  val baas = new BAAS(actorSystem)

  //Add the implementation to the BAASAPI
  val baasClient: BAASClient = new BAASClient(s"$host", port)(actorSystem)
  baasClient.addImplementation(InteractionOne())
}

