package com.ing.baker.baas.akka

import akka.actor.ExtendedActorSystem
import com.ing.baker.baas.protocol.ProtocolDistributedEventPublishing
import com.ing.baker.runtime.serialization.TypedProtobufSerializer.BinarySerializable
import com.ing.baker.runtime.serialization.{SerializersProvider, TypedProtobufSerializer}
import com.ing.baker.runtime.serialization.TypedProtobufSerializer.forType
import com.ing.baker.baas.protocol.DistributedEventPublishingProto._

object ProtobufSerializer {

  def entries(ev0: SerializersProvider): List[BinarySerializable] = {
    implicit val ev = ev0
    List(
      forType[ProtocolDistributedEventPublishing.Event]
        .register("ProtocolDistributedEventPublishing.Event")
    )
  }
}

class ProtobufSerializer(system: ExtendedActorSystem) extends TypedProtobufSerializer(system, ProtobufSerializer.entries)
