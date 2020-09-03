package com.ing.baker.runtime.serialization.protomappings
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.scaladsl.SensoryEventResult
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.baker.types.Value
import scalapb.GeneratedMessageCompanion

import scala.util.Try

class SensoryEventResultMapping(implicit valueProto: ProtoMap[Value, protobuf.Value]) extends ProtoMap[SensoryEventResult, protobuf.SensoryEventResult] {

  override def companion: GeneratedMessageCompanion[protobuf.SensoryEventResult] =
    protobuf.SensoryEventResult

  override def toProto(a: SensoryEventResult): protobuf.SensoryEventResult =
    protobuf.SensoryEventResult(
      Some(SensoryEventStatusMappingHelper.toProto(a.sensoryEventStatus)),
      a.eventNames,
      a.ingredients.mapValues(ctxToProto(_))
    )

  override def fromProto(message: protobuf.SensoryEventResult): Try[SensoryEventResult] =
    for {
      protoStatus <- versioned(message.status, "status")
      status <- SensoryEventStatusMappingHelper.fromProto(protoStatus)
      events = message.events
      ingredients <- message.ingredients.toList.traverse { case (name, value) =>
        ctxFromProto(value).map(name -> _)
      }
    } yield SensoryEventResult(status, events, ingredients.toMap)
}
