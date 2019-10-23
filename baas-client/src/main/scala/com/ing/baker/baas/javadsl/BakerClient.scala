package com.ing.baker.baas.javadsl

import akka.actor.ActorSystem
import akka.stream.Materializer
import com.ing.baker.runtime.akka.actor.serialization.Encryption
import com.ing.baker.baas.scaladsl.{BakerClient => ScalaRemoteBaker}
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.javadsl.{Baker => JavaBaker}

object BakerClient {

  def build(hostname: String, actorSystem: ActorSystem, mat: Materializer, encryption: Encryption = Encryption.NoEncryption): JavaBaker =
    AkkaBaker.javaOther(ScalaRemoteBaker.build(hostname, encryption)(actorSystem, mat))
}
