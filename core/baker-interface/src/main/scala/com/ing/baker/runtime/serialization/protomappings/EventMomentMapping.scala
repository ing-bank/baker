package com.ing.baker.runtime.serialization.protomappings

import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.scaladsl.EventMoment
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.baker.runtime.serialization.ProtoMap.versioned

import scala.util.Try

class EventMomentMapping extends ProtoMap[EventMoment, protobuf.EventMoment] {

  val companion = protobuf.EventMoment

  override def toProto(a: EventMoment): protobuf.EventMoment = {
    protobuf.EventMoment(Some(a.name), Some(a.occurredOn))
  }

  override def fromProto(message: protobuf.EventMoment): Try[EventMoment] =
    for {
      name <- versioned(message.name, "name")
    } yield EventMoment(name, message.occurredOn.getOrElse(0L))
}
