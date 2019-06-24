package com.ing.baker.runtime.akka.actor.serialization.protomappings

import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.versioned
import com.ing.baker.runtime.scaladsl.EventMoment

import scala.util.Try

class EventMomentMapping extends ProtoMap[EventMoment, protobuf.EventMoment] {

  val companion = protobuf.EventMoment

  override def toProto(a: EventMoment): protobuf.EventMoment = {
    protobuf.EventMoment(Some(a.name), Some(a.occurredOn))
  }

  override def fromProto(message: protobuf.EventMoment): Try[EventMoment] =
    for {
      name <- versioned(message.name, "name")
    } yield EventMoment(name, message.occurredOn.getOrElse(0l))
}
