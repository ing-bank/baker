package com.ing.baker.runtime.baas.javadsl

import akka.actor.ActorSystem
import akka.stream.Materializer
import com.ing.baker.runtime.akka.actor.serialization.Encryption
import com.ing.baker.runtime.baas.scaladsl.{ Baker => ScalaRemoteBaker }
import com.ing.baker.runtime.javadsl.{ Baker => JavaBaker }

object Baker {

  def remote(hostname: String, actorSystem: ActorSystem, mat: Materializer, encryption: Encryption = Encryption.NoEncryption): JavaBaker =
    new JavaBaker(ScalaRemoteBaker.remote(hostname, encryption)(actorSystem, mat))
}
