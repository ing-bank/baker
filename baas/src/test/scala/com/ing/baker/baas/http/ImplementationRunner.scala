package com.ing.baker.baas.http

import com.ing.baker.baas.BAASSpec.InteractionOne
import com.ing.baker.baas.{BAAS, BAASClient}

class ImplementationRunner {
}
object ImplementationRunner extends App {

  val host = "localhost"
  val port = 8081
  val baas = new BAAS()

  //Add the implementation to the BAASAPI
  val baasClient: BAASClient = new BAASClient(s"$host", port)
  baasClient.addImplementation(InteractionOne())
}

