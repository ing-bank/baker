package com.ing.baker.baas.akka

import akka.actor.ExtendedActorSystem
import com.ing.baker.runtime.scaladsl.BakerEvent
import com.ing.baker.runtime.serialization.TypedProtobufSerializer.{BinarySerializable, forType}
import com.ing.baker.runtime.serialization.{SerializersProvider, TypedProtobufSerializer}

object DistributedBakerEventPublishingProtocolSerializer {

  val identifier: Int = 104

  def entries(ev0: SerializersProvider): List[BinarySerializable] = {
    implicit val ev = ev0
    List(
      forType[BakerEvent]
        .register("DistributedBakerEventPublishingProtocolSerializer.BakerEvent")
    )
  }
}

class DistributedBakerEventPublishingProtocolSerializer(system: ExtendedActorSystem) extends TypedProtobufSerializer(
  system,
  DistributedBakerEventPublishingProtocolSerializer.identifier,
  DistributedBakerEventPublishingProtocolSerializer.entries
)
