package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.runtime.actor.serialization.{ProtoEventAdapter, ProtoEventAdapterModule}
import com.ing.baker.runtime.core.{protobuf, BakerResponseEventProtocol => protocol}

class BakerResponseEventProtocolModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case protocol.InstanceTransitionFired(data) =>
      protobuf.InstanceTransitionFired(Some(ctx.toProtoAny(data.asInstanceOf[AnyRef])))

    case protocol.InstanceTransitionNotEnabled(data) =>
      protobuf.InstanceTransitionNotEnabled(Some(ctx.toProtoAny(data.asInstanceOf[AnyRef])))

    case protocol.InstanceAlreadyReceived(data) =>
      protobuf.InstanceAlreadyReceived(Some(ctx.toProtoAny(data.asInstanceOf[AnyRef])))

    case protocol.IndexNoSuchProcess(data) =>
      protobuf.IndexNoSuchProcess(Some(ctx.toProtoAny(data.asInstanceOf[AnyRef])))

    case protocol.IndexReceivePeriodExpired(data) =>
      protobuf.IndexReceivePeriodExpired(Some(ctx.toProtoAny(data.asInstanceOf[AnyRef])))

    case protocol.IndexProcessDeleted(data) =>
      protobuf.IndexProcessDeleted(Some(ctx.toProtoAny(data.asInstanceOf[AnyRef])))

    case protocol.IndexInvalidEvent(data) =>
      protobuf.IndexInvalidEvent(Some(ctx.toProtoAny(data.asInstanceOf[AnyRef])))
  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {
    case protobuf.InstanceTransitionFired(Some(data)) =>
      protocol.InstanceTransitionFired(data)

    case protobuf.InstanceTransitionNotEnabled(Some(data)) =>
      protocol.InstanceTransitionNotEnabled(data)

    case protobuf.InstanceAlreadyReceived(Some(data)) =>
      protocol.InstanceAlreadyReceived(data)

    case protobuf.IndexNoSuchProcess(Some(data)) =>
      protocol.IndexNoSuchProcess(data)

    case protobuf.IndexReceivePeriodExpired(Some(data)) =>
      protocol.IndexReceivePeriodExpired(data)

    case protobuf.IndexProcessDeleted(Some(data)) =>
      protocol.IndexProcessDeleted(data)

    case protobuf.IndexInvalidEvent(Some(data)) =>
      protocol.IndexInvalidEvent(data)
  }
}
