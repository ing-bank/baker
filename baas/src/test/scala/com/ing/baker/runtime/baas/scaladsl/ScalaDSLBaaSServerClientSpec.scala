package com.ing.baker.runtime.baas.scaladsl

import akka.actor.ActorSystem
import akka.http.scaladsl.model.Uri
import akka.stream.{ActorMaterializer, Materializer}
import cats.arrow.FunctionK
import cats.~>
import com.ing.baker.runtime.baas.common.CommonBaaSServerClientSpec
import com.ing.baker.runtime.scaladsl.{Baker => ScalaBaker}

import scala.concurrent.Future
import ScalaDSLBaaSServerClientSpec._
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi

object ScalaDSLBaaSServerClientSpec {

  implicit val system: ActorSystem = ActorSystem("ScalaDSLBaaSServerClientSpec")

  implicit val materializer: Materializer = ActorMaterializer()

  val host: String = "localhost"

  val port: Int = 8181

  val clientBaker = new Baker(Uri(s"http://$host:$port"))

  val serverBaker = ScalaBaker.akkaLocalDefault(system, materializer)

  val IdentityFuture: Future ~> Future = FunctionK.id
}

class ScalaDSLBaaSServerClientSpec extends CommonBaaSServerClientSpec(clientBaker, serverBaker, host, port, IdentityFuture) with ScalaApi

