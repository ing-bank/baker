package com.ing.baker.baas.http

import akka.actor.ActorSystem
import com.ing.baker.baas.BAAS

object BAASAPISpec extends App {
  new BAASAPI(new BAAS())(ActorSystem("BAASAPIActorSystem")).start()
}

class BAASAPISpec {

}
