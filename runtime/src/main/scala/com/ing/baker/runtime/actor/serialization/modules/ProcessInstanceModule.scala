package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.petrinet.api.MultiSet
import com.ing.baker.petrinet.runtime.ExceptionStrategy
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol.MarkingData
import com.ing.baker.runtime.actor.process_instance.protobuf.FailureStrategyMessage.StrategyTypeMessage
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
    case protocol.TransitionFired(jobId, transitionId, correlationId, consumed, produced, state, newJobs, output) =>
      protobuf.TransitionFiredMessage(Some(jobId), Some(transitionId), correlationId,
        markingDataToProto(consumed, ctx), markingDataToProto(produced, ctx), null,
        newJobs.toSeq, Some(ctx.toProtoUnkown(output.asInstanceOf[AnyRef])))
    case protocol.InstanceState(sequenceNr, marking, state, jobs) =>
      protobuf.InstanceState(Some(sequenceNr), markingDataToProto(marking, ctx),
        Some(ctx.toProtoUnkown(state.asInstanceOf[AnyRef])),
        jobs.values.map(job => ctx.toProto[protobuf.JobState](job)).toSeq)
    case protocol.JobState(jobId, transitionId, consumed, input, exceptionState) =>
      protobuf.JobState(Some(jobId), Some(transitionId), markingDataToProto(consumed, ctx),
        Some(ctx.toProtoUnkown(input.asInstanceOf[AnyRef])), Some(ctx.toProto[protobuf.ExceptionState](exceptionState)))
    case protocol.ExceptionState(failureCount, failureReason, failureStrategy) =>
      protobuf.ExceptionState(Some(failureCount), Some(failureReason), Some(ctx.toProto[protobuf.FailureStrategy](failureStrategy)))
    case exceptionStrategy: ExceptionStrategy => exceptionStrategy match {
      case ExceptionStrategy.Fatal => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.FATAL), None)
      case ExceptionStrategy.BlockTransition => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.BLOCK_TRANSITION), None)
      case ExceptionStrategy.Continue(marking, output) => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.CONTINUE), None)
      case ExceptionStrategy.RetryWithDelay(delay) => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.RETRY), Some(delay))
    }
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
