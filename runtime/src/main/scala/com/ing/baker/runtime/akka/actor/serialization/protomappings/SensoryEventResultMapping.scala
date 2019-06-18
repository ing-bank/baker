package com.ing.baker.runtime.akka.actor.serialization.protomappings

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.scaladsl.SensoryEventResult
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.types.Value
import scalapb.GeneratedMessageCompanion

import scala.util.{Failure, Success, Try}

class SensoryEventResultMapping(implicit valueProto: ProtoMap[Value, protobuf.Value]) extends ProtoMap[SensoryEventResult, protobuf.SensoryEventResult] {

  override def companion: GeneratedMessageCompanion[protobuf.SensoryEventResult] =
    protobuf.SensoryEventResult

  override def toProto(a: SensoryEventResult): protobuf.SensoryEventResult =
    protobuf.SensoryEventResult(
      Some(a.status match {
        case SensoryEventStatus.Received => protobuf.SensoryEventStatus.RECEIVED
        case SensoryEventStatus.Completed => protobuf.SensoryEventStatus.COMPLETED
        case SensoryEventStatus.FiringLimitMet => protobuf.SensoryEventStatus.FIRING_LIMIT_MET
        case SensoryEventStatus.ReceivePeriodExpired => protobuf.SensoryEventStatus.RECEIVE_PERIOD_EXPIRED
        case SensoryEventStatus.AlreadyReceived => protobuf.SensoryEventStatus.ALREADY_RECEIVED
        case SensoryEventStatus.ProcessDeleted => protobuf.SensoryEventStatus.PROCESS_DELETED
      }),
      a.events,
      a.ingredients.mapValues(ctxToProto(_))
    )

  override def fromProto(message: protobuf.SensoryEventResult): Try[SensoryEventResult] =
    for {
      protoStatus <- versioned(message.status, "status")
      status <- protoStatus match {
        case protobuf.SensoryEventStatus.RECEIVED => Success(SensoryEventStatus.Received)
        case protobuf.SensoryEventStatus.COMPLETED => Success(SensoryEventStatus.Completed)
        case protobuf.SensoryEventStatus.FIRING_LIMIT_MET => Success(SensoryEventStatus.FiringLimitMet)
        case protobuf.SensoryEventStatus.RECEIVE_PERIOD_EXPIRED => Success(SensoryEventStatus.ReceivePeriodExpired)
        case protobuf.SensoryEventStatus.ALREADY_RECEIVED => Success(SensoryEventStatus.AlreadyReceived)
        case protobuf.SensoryEventStatus.PROCESS_DELETED => Success(SensoryEventStatus.ProcessDeleted)
        case protobuf.SensoryEventStatus.Unrecognized(value) => Failure(new IllegalStateException(s"Received illegal value '$value' for enumeration SensoryEventStatus"))
      }
      events = message.events
      ingredients <- message.ingredients.toList.traverse { case (name, value) =>
        ctxFromProto(value).map(name -> _)
      }
    } yield SensoryEventResult(status, events, ingredients.toMap)
}
