package com.ing.baker.runtime.akka.actor.serialization

import org.apache.pekko.actor.ActorSystem
import org.apache.pekko.serialization.{Serialization, SerializationExtension, Serializer}
import com.ing.baker.runtime.serialization.Encryption

case class AkkaSerializerProvider(getSerializerFor: AnyRef => Serializer, serializerByIdentity: Int => Option[Serializer], encryption: Encryption)

object AkkaSerializerProvider {

  def apply(system: ActorSystem, encryption: Encryption): AkkaSerializerProvider = {
    val serialization: Serialization = SerializationExtension.get(system)
    AkkaSerializerProvider(
      serialization.findSerializerFor,
      serialization.serializerByIdentity.get,
      encryption
    )
  }
}
