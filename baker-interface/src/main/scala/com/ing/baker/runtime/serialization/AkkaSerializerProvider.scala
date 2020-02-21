package com.ing.baker.runtime.serialization

import akka.actor.ActorSystem
import akka.serialization.{Serialization, SerializationExtension, Serializer}

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
