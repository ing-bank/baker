package com.ing.baker.baas.mocks

import akka.actor.ActorSystem
import com.ing.baker.runtime.serialization.{Encryption, ProtoMap, SerializersProvider}

object Utils {

  private type ProtoMessage[A] = scalapb.GeneratedMessage with scalapb.Message[A]

  def serialize[A, P <: ProtoMessage[P]](message: A)(implicit mapping: ProtoMap[A, P]): Array[Byte] =
    mapping.toByteArray(message)

  implicit def serializersProvider(implicit system: ActorSystem, encryption: Encryption): SerializersProvider =
    SerializersProvider(system, encryption)
}
