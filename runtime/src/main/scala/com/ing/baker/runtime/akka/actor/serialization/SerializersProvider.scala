package com.ing.baker.runtime.akka.actor.serialization

import akka.actor.{ActorRefProvider, ActorSystem}
import akka.serialization.{Serialization, SerializationExtension, Serializer}

case class SerializersProvider(getSerializerFor: AnyRef => Serializer, serializerByIdentity: Int => Option[Serializer], encryption: Encryption, actorRefProvider: ActorRefProvider)

object SerializersProvider {

  def apply(system: ActorSystem, actorRefProvider: ActorRefProvider, encryption: Encryption): SerializersProvider = {
    val serialization: Serialization = SerializationExtension.get(system)
    SerializersProvider(
      serialization.findSerializerFor,
      serialization.serializerByIdentity.get,
      encryption,
      actorRefProvider
    )
  }

  def apply(system: ActorSystem, actorRefProvider: ActorRefProvider): SerializersProvider = {
    apply(system, actorRefProvider, Encryption.NoEncryption)
  }

  def apply(system: ActorSystem, encryption: Encryption): SerializersProvider = {
    apply(system, null, encryption)
  }

  def apply(system: ActorSystem): SerializersProvider = {
    apply(system, null, Encryption.NoEncryption)
  }
}
