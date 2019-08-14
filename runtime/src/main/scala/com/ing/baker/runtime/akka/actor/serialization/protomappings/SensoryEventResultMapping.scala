package com.ing.baker.runtime.akka.actor.serialization.protomappings

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.scaladsl.EventResult
import com.ing.baker.types.Value
import scalapb.GeneratedMessageCompanion

import scala.util.Try

class SensoryEventResultMapping(implicit valueProto: ProtoMap[Value, protobuf.Value]) extends ProtoMap[EventResult, protobuf.SensoryEventResult] {

  override def companion: GeneratedMessageCompanion[protobuf.SensoryEventResult] =
    protobuf.SensoryEventResult

  override def toProto(a: EventResult): protobuf.SensoryEventResult =
    protobuf.SensoryEventResult(
      Some(SensoryEventStatusMappingHelper.toProto(a.status)),
      a.events,
      a.ingredients.mapValues(ctxToProto(_))
    )

  override def fromProto(message: protobuf.SensoryEventResult): Try[EventResult] =
    for {
      protoStatus <- versioned(message.status, "status")
      status <- SensoryEventStatusMappingHelper.fromProto(protoStatus)
      events = message.events
      ingredients <- message.ingredients.toList.traverse { case (name, value) =>
        ctxFromProto(value).map(name -> _)
      }
    } yield EventResult(status, events, ingredients.toMap)
}
