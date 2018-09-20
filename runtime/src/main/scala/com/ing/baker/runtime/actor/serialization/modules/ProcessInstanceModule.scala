package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.petrinet.api.MultiSet
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol.MarkingData
import com.ing.baker.runtime.actor.process_instance.{protobuf, ProcessInstanceProtocol => protocol}

class ProcessInstanceModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case protocol.GetState =>
      protobuf.GetState()
    case protocol.Stop(delete) =>
      protobuf.Stop(Some(delete))
    case protocol.Initialize(marking, state) =>
      protobuf.Initialize(
        markingDataToProto(marking, ctx),
        Some(ctx.toProtoUnkown(state.asInstanceOf[AnyRef])))
  }

  private def markingDataToProto(markingData: MarkingData, ctx: ProtoEventAdapter): Seq[protobuf.MarkingData] = {
    markingData.flatMap { case (placeId, multiSet) =>
      multiSet.map { case (data, count) =>
        protobuf.MarkingData(Some(placeId), Some(ctx.toProtoUnkown(data.asInstanceOf[AnyRef])), Some(count))
      }
    }.toSeq
  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {
    case protobuf.GetState() =>
      protocol.GetState
    case protobuf.Stop(Some(delete)) =>
      protocol.Stop(delete)
    case protobuf.Initialize(markingData, Some(state)) =>
      protocol.Initialize(
        protoToMarkingData(markingData, ctx),
        ctx.toDomain[Any](state))

  }

  private def protoToMarkingData(markingData: Seq[protobuf.MarkingData], ctx: ProtoEventAdapter): protocol.MarkingData = {
    markingData.foldLeft[MarkingData](Map.empty) {
      case (acc, protobuf.MarkingData(Some(placeId), Some(data), Some(count))) =>
        val placeData: MultiSet[AnyRef] = acc.get(placeId).map(_.asInstanceOf[MultiSet[AnyRef]]).getOrElse(MultiSet.empty)
        val deserializedData = ctx.toDomain[AnyRef](data)
        acc + (placeId -> (placeData + (deserializedData -> count)))
      case _ => throw new IllegalStateException("missing data in serialized data when deserializing MarkingData")
    }
  }
}
