package com.ing.baker.runtime.actor.serialization

import akka.actor.{ActorRefProvider, ActorSystem}
import akka.serialization.{Serialization, SerializationExtension, Serializer}

case class SerializersProvider(getSerializerFor: AnyRef => Serializer, serializerByIdentity: Int => Option[Serializer], encryption: Encryption, actorRefProvider: ActorRefProvider)

object SerializersProvider {

  def apply(system: ActorSystem, actorRefProvider: ActorRefProvider, encryption: Encryption = Encryption.NoEncryption): SerializersProvider = {
    val serialization: Serialization = SerializationExtension.get(system)
    SerializersProvider(
      serialization.findSerializerFor,
      serialization.serializerByIdentity.get,
      encryption,
      actorRefProvider
    )
  }
}
