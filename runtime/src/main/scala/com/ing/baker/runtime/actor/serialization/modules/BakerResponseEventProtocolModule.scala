package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.runtime.actor.serialization.{ProtoEventAdapter, ProtoEventAdapterModule}
import com.ing.baker.runtime.core.{protobuf, BakerResponseEventProtocol => protocol}

class BakerResponseEventProtocolModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case protocol.InstanceTransitionFired =>
      protobuf.InstanceTransitionFired()

    case protocol.InstanceTransitionNotEnabled =>
      protobuf.InstanceTransitionNotEnabled()

    case protocol.InstanceAlreadyReceived =>
      protobuf.InstanceAlreadyReceived()

    case protocol.IndexNoSuchProcess(processId) =>
      protobuf.IndexNoSuchProcess(Some(processId))

    case protocol.IndexReceivePeriodExpired =>
      protobuf.IndexReceivePeriodExpired()

    case protocol.IndexProcessDeleted =>
      protobuf.IndexProcessDeleted()

    case protocol.IndexInvalidEvent(invalidEventMessage) =>
      protobuf.IndexInvalidEvent(Some(invalidEventMessage))
  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {
    case protobuf.InstanceTransitionFired() =>
      protocol.InstanceTransitionFired

    case protobuf.InstanceTransitionNotEnabled() =>
      protocol.InstanceTransitionNotEnabled

    case protobuf.InstanceAlreadyReceived() =>
      protocol.InstanceAlreadyReceived

    case protobuf.IndexNoSuchProcess(Some(processId)) =>
      protocol.IndexNoSuchProcess(processId)

    case protobuf.IndexReceivePeriodExpired() =>
      protocol.IndexReceivePeriodExpired

    case protobuf.IndexProcessDeleted() =>
      protocol.IndexProcessDeleted

    case protobuf.IndexInvalidEvent(Some(invalidEventMessage)) =>
      protocol.IndexInvalidEvent(invalidEventMessage)
  }
}
