package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.runtime.actor.serialization.{ProtoEventAdapter, ProtoEventAdapterModule}
import com.ing.baker.runtime.core.{protobuf, BakerResponseEventProtocol => protocol}
import com.ing.baker.runtime.actor.process_index.{ProcessIndexProtocol => idxProtocol}
import com.ing.baker.runtime.actor.process_instance.{ProcessInstanceProtocol => insProtocol}
import com.ing.baker.runtime.actor.process_index.{protobuf => idxProto}
import com.ing.baker.runtime.actor.process_instance.{protobuf => insProto}

class BakerResponseEventProtocolModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {

    case protocol.InstanceTransitionFired(data) =>
      protobuf.BakerResponseEventProtocol().withInsTransitionFired(
        protobuf.InstanceTransitionFired(Some(ctx.toProto[insProto.TransitionFiredMessage](data)))
      )

    case protocol.InstanceTransitionNotEnabled(data) =>
      protobuf.BakerResponseEventProtocol().withInsTransitionNotEnabled(
        protobuf.InstanceTransitionNotEnabled(Some(ctx.toProto[insProto.TransitionNotEnabled](data)))
      )

    case protocol.InstanceAlreadyReceived(data) =>
      protobuf.BakerResponseEventProtocol().withInsAlreadyReceived(
        protobuf.InstanceAlreadyReceived(Some(ctx.toProto[insProto.AlreadyReceived](data)))
      )

    case protocol.IndexNoSuchProcess(data) =>
      protobuf.BakerResponseEventProtocol().withIdxNoSuchProcess(
        protobuf.IndexNoSuchProcess(Some(ctx.toProto[idxProto.NoSuchProcess](data)))
      )

    case protocol.IndexReceivePeriodExpired(data) =>
      protobuf.BakerResponseEventProtocol().withIdxReceivedPeriodExpired(
        protobuf.IndexReceivePeriodExpired(Some(ctx.toProto[idxProto.ReceivePeriodExpired](data)))
      )

    case protocol.IndexProcessDeleted(data) =>
      protobuf.BakerResponseEventProtocol().withIdxProcessDeleted(
        protobuf.IndexProcessDeleted(Some(ctx.toProto[idxProto.ProcessDeleted](data)))
      )

    case protocol.IndexInvalidEvent(data) =>
      protobuf.BakerResponseEventProtocol().withIdxInvalidEvent(
        protobuf.IndexInvalidEvent(Some(ctx.toProto[idxProto.InvalidEvent](data)))
      )
  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {

    case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isInsTransitionFired =>
      protocol.InstanceTransitionFired(ctx.toDomain[insProtocol.TransitionFired](message.getInsTransitionFired.data.get))

    case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isInsTransitionNotEnabled =>
      protocol.InstanceTransitionNotEnabled(ctx.toDomain[insProtocol.TransitionNotEnabled](message.getInsTransitionNotEnabled.data.get))

    case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isInsAlreadyReceived =>
      protocol.InstanceAlreadyReceived(ctx.toDomain[insProtocol.AlreadyReceived](message.getInsAlreadyReceived.data.get))

    case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isIdxNoSuchProcess =>
      protocol.IndexNoSuchProcess(ctx.toDomain[idxProtocol.NoSuchProcess](message.getIdxNoSuchProcess.data.get))

    case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isIdxReceivedPeriodExpired =>
      protocol.IndexReceivePeriodExpired(ctx.toDomain[idxProtocol.ReceivePeriodExpired](message.getIdxReceivedPeriodExpired.data.get))

    case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isIdxProcessDeleted =>
      protocol.IndexProcessDeleted(ctx.toDomain[idxProtocol.ProcessDeleted](message.getIdxProcessDeleted.data.get))

    case message: protobuf.BakerResponseEventProtocol if message.sealedValue.isIdxInvalidEvent =>
      protocol.IndexInvalidEvent(ctx.toDomain[idxProtocol.InvalidEvent](message.getIdxInvalidEvent.data.get))

  }
}
