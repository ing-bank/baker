package com.ing.baker.baas.akka

import akka.actor.ExtendedActorSystem
import com.ing.baker.baas.protocol.DistributedEventPublishingProto._
import com.ing.baker.baas.protocol.ProtocolDistributedEventPublishing
import com.ing.baker.runtime.serialization.TypedProtobufSerializer.{BinarySerializable, forType}
import com.ing.baker.runtime.serialization.{AkkaSerializerProvider, TypedProtobufSerializer}

object DistributedEventPublishingProtocolSerializer {

  val identifier: Int = 103

  def entries(ev0: AkkaSerializerProvider): List[BinarySerializable] = {
    implicit val ev = ev0
    List(
      forType[ProtocolDistributedEventPublishing.Event]
        .register("ProtocolDistributedEventPublishing.Event")
    )
  }
}

class DistributedEventPublishingProtocolSerializer(system: ExtendedActorSystem) extends TypedProtobufSerializer(
  system,
  DistributedEventPublishingProtocolSerializer.identifier,
  DistributedEventPublishingProtocolSerializer.entries
)
