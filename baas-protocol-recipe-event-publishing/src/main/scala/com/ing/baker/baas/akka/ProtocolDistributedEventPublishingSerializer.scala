package com.ing.baker.baas.akka

import akka.actor.ExtendedActorSystem
import com.ing.baker.baas.protocol.DistributedEventPublishingProto._
import com.ing.baker.baas.protocol.ProtocolDistributedEventPublishing
import com.ing.baker.runtime.serialization.TypedProtobufSerializer.{BinarySerializable, forType}
import com.ing.baker.runtime.serialization.{SerializersProvider, TypedProtobufSerializer}

object ProtocolDistributedEventPublishingSerializer {

  def entries(ev0: SerializersProvider): List[BinarySerializable] = {
    implicit val ev = ev0
    List(
      forType[ProtocolDistributedEventPublishing.Event]
        .register("ProtocolDistributedEventPublishing.Event")
    )
  }
}

class ProtocolDistributedEventPublishingSerializer(system: ExtendedActorSystem) extends TypedProtobufSerializer(system, ProtocolDistributedEventPublishingSerializer.entries)
