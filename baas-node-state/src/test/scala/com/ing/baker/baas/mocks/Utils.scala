package com.ing.baker.baas.mocks

import akka.actor.ActorSystem
import com.ing.baker.runtime.akka.actor.serialization.AkkaSerializerProvider
import com.ing.baker.runtime.serialization.{Encryption, ProtoMap}

object Utils {

  private type ProtoMessage[A] = scalapb.GeneratedMessage

  def serialize[A, P <: ProtoMessage[P]](message: A)(implicit mapping: ProtoMap[A, P]): Array[Byte] =
    mapping.toByteArray(message)

  implicit def serializersProvider(implicit system: ActorSystem, encryption: Encryption): AkkaSerializerProvider =
    AkkaSerializerProvider(system, encryption)
}
