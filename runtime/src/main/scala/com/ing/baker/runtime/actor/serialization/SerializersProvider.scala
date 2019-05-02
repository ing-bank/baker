package com.ing.baker.runtime.actor.serialization

import akka.actor.ActorSystem
import akka.serialization.{Serialization, SerializationExtension, Serializer}

case class SerializersProvider(getSerializerFor: AnyRef => Serializer, serializerByIdentity: Int => Option[Serializer], encryption: Encryption)

object SerializersProvider {

  def apply(system: ActorSystem, encryption: Encryption = Encryption.NoEncryption): SerializersProvider = {
    val serialization: Serialization = SerializationExtension.get(system)
    SerializersProvider(
      serialization.findSerializerFor,
      serialization.serializerByIdentity.get,
      encryption
    )
  }
}
