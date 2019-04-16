package com.ing.baker.runtime.core

import akka.util.ByteString
import com.ing.baker.runtime.actor.process_index.{ProcessIndexProtocol => idxProtocol}
import com.ing.baker.runtime.actor.process_instance.{ProcessInstanceProtocol => insProtocol}
import com.ing.baker.runtime.actortyped.serialization.{ProtoMap, SerializersProvider}
import com.ing.baker.runtime.actortyped.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.actor.process_index.ProcessIndexProto._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProto._
import scalapb.GeneratedMessageCompanion

import scala.util.Try

sealed trait BakerResponseEventProtocol {

  def toSensoryEventStatus: SensoryEventStatus = this match {
    case BakerResponseEventProtocol.InstanceTransitionFired(_) =>
      SensoryEventStatus.Received

    case BakerResponseEventProtocol.InstanceTransitionNotEnabled(_) =>
      SensoryEventStatus.FiringLimitMet

    case BakerResponseEventProtocol.InstanceAlreadyReceived(_) =>
      SensoryEventStatus.AlreadyReceived

    case BakerResponseEventProtocol.IndexNoSuchProcess(event) =>
      throw new NoSuchProcessException(s"No such process: ${event.asInstanceOf[idxProtocol.NoSuchProcess].processId}")

    case BakerResponseEventProtocol.IndexReceivePeriodExpired(_) =>
      SensoryEventStatus.ReceivePeriodExpired

    case BakerResponseEventProtocol.IndexProcessDeleted(_) =>
      SensoryEventStatus.ProcessDeleted

    case BakerResponseEventProtocol.IndexInvalidEvent(event) =>
      throw new IllegalArgumentException(event.asInstanceOf[idxProtocol.InvalidEvent].msg)

    case msg@_ => throw new BakerException(s"Unexpected transformation to event status: $msg")
  }

}

object BakerResponseEventProtocol {

  def SerializationDelimiter: ByteString = ByteString("|>|>|>")

  case class InstanceTransitionFired(value: insProtocol.TransitionFired) extends BakerResponseEventProtocol

  case class InstanceTransitionNotEnabled(value: insProtocol.TransitionNotEnabled) extends BakerResponseEventProtocol

  case class InstanceTransitionFailed(value: insProtocol.TransitionFailed) extends BakerResponseEventProtocol

  case class InstanceAlreadyReceived(value: insProtocol.AlreadyReceived) extends BakerResponseEventProtocol

  case class IndexNoSuchProcess(value: idxProtocol.NoSuchProcess) extends BakerResponseEventProtocol

  case class IndexReceivePeriodExpired(value: idxProtocol.ReceivePeriodExpired) extends BakerResponseEventProtocol

  case class IndexProcessDeleted(value: idxProtocol.ProcessDeleted) extends BakerResponseEventProtocol

  case class IndexInvalidEvent(value: idxProtocol.InvalidEvent) extends BakerResponseEventProtocol

  def fromProtocols(msg: Any): BakerResponseEventProtocol = msg match {
    case event: insProtocol.TransitionFired => InstanceTransitionFired(event)
    case event: insProtocol.TransitionNotEnabled => InstanceTransitionNotEnabled(event)
    case event: insProtocol.TransitionFailed => InstanceTransitionFailed(event)
    case event: insProtocol.AlreadyReceived => InstanceAlreadyReceived(event)
    case event: idxProtocol.NoSuchProcess => IndexNoSuchProcess(event)
    case event: idxProtocol.ReceivePeriodExpired => IndexReceivePeriodExpired(event)
    case event: idxProtocol.ProcessDeleted => IndexProcessDeleted(event)
    case event: idxProtocol.InvalidEvent => IndexInvalidEvent(event)
    case msg@_ => throw new BakerException(s"Unexpected protocol message: $msg")
  }

  implicit def protoMap(implicit ev0: SerializersProvider): ProtoMap[BakerResponseEventProtocol, protobuf.BakerResponseEventProtocol] =
    new ProtoMap[BakerResponseEventProtocol, protobuf.BakerResponseEventProtocol] {

      override def companion: GeneratedMessageCompanion[protobuf.BakerResponseEventProtocol] =
        protobuf.BakerResponseEventProtocol

      override def toProto(a: BakerResponseEventProtocol): protobuf.BakerResponseEventProtocol =
        a match {
          case InstanceTransitionFired(data) =>
            protobuf.BakerResponseEventProtocol().withInsTransitionFired(
              protobuf.InstanceTransitionFired(Some(ctxToProto(data)))
            )

          case InstanceTransitionNotEnabled(data) =>
            protobuf.BakerResponseEventProtocol().withInsTransitionNotEnabled(
              protobuf.InstanceTransitionNotEnabled(Some(ctxToProto(data)))
            )

          case InstanceTransitionFailed(data) =>
            protobuf.BakerResponseEventProtocol().withInsTransitionFailed(
              protobuf.InstanceTransitionFailed(Some(ctxToProto(data)))
            )

          case InstanceAlreadyReceived(data) =>
            protobuf.BakerResponseEventProtocol().withInsAlreadyReceived(
              protobuf.InstanceAlreadyReceived(Some(ctxToProto(data)))
            )

          case IndexNoSuchProcess(data) =>
            protobuf.BakerResponseEventProtocol().withIdxNoSuchProcess(
              protobuf.IndexNoSuchProcess(Some(ctxToProto(data)))
            )

          case IndexReceivePeriodExpired(data) =>
            protobuf.BakerResponseEventProtocol().withIdxReceivedPeriodExpired(
              protobuf.IndexReceivePeriodExpired(Some(ctxToProto(data)))
            )

          case IndexProcessDeleted(data) =>
            protobuf.BakerResponseEventProtocol().withIdxProcessDeleted(
              protobuf.IndexProcessDeleted(Some(ctxToProto(data)))
            )

          case IndexInvalidEvent(data) =>
            protobuf.BakerResponseEventProtocol().withIdxInvalidEvent(
              protobuf.IndexInvalidEvent(Some(ctxToProto(data)))
            )
        }

      override def fromProto(message: protobuf.BakerResponseEventProtocol): Try[BakerResponseEventProtocol] =
        message match {
          case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isInsTransitionFired =>
            versioned(message.getInsTransitionFired.data, "data")
              .flatMap(ctxFromProto(_))
              .map(InstanceTransitionFired)

          case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isInsTransitionNotEnabled =>
            versioned(message.getInsTransitionNotEnabled.data, "data")
              .flatMap(ctxFromProto(_))
              .map(InstanceTransitionNotEnabled)

          case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isInsTransitionFailed =>
            versioned(message.getInsTransitionFailed.data, "data")
              .flatMap(ctxFromProto(_))
              .map(InstanceTransitionFailed)

          case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isInsAlreadyReceived =>
            versioned(message.getInsAlreadyReceived.data, "data")
              .flatMap(ctxFromProto(_))
              .map(InstanceAlreadyReceived)

          case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isIdxNoSuchProcess =>
            versioned(message.getIdxNoSuchProcess.data, "data")
              .flatMap(ctxFromProto(_))
              .map(IndexNoSuchProcess)

          case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isIdxReceivedPeriodExpired =>
            versioned(message.getIdxReceivedPeriodExpired.data, "data")
              .flatMap(ctxFromProto(_))
              .map(IndexReceivePeriodExpired)

          case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isIdxProcessDeleted =>
            versioned(message.getIdxProcessDeleted.data, "data")
              .flatMap(ctxFromProto(_))
              .map(IndexProcessDeleted)

          case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isIdxInvalidEvent =>
            versioned(message.getIdxInvalidEvent.data, "data")
              .flatMap(ctxFromProto(_))
              .map(IndexInvalidEvent)
        }
    }

}
