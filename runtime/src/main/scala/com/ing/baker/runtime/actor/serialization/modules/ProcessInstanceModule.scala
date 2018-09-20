package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.petrinet.api.MultiSet
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol.{ExceptionStrategy, MarkingData}
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
        markingDataToProto(consumed, ctx), markingDataToProto(produced, ctx), Some(ctx.toProto[protobuf.InstanceState](state)),
        newJobs.toSeq, Some(ctx.toProtoUnkown(output.asInstanceOf[AnyRef])))
    case protocol.InstanceState(sequenceNr, marking, state, jobs) =>
      protobuf.InstanceState(Some(sequenceNr), markingDataToProto(marking, ctx),
        Some(ctx.toProtoUnkown(state.asInstanceOf[AnyRef])),
        jobs.values.map(job => ctx.toProto[protobuf.JobState](job)).toSeq)
    case protocol.JobState(jobId, transitionId, consumed, input, exceptionState) =>
      protobuf.JobState(Some(jobId), Some(transitionId), markingDataToProto(consumed, ctx),
        Some(ctx.toProtoUnkown(input.asInstanceOf[AnyRef])), exceptionState.map(ctx.toProto[protobuf.ExceptionState]))
    case protocol.ExceptionState(failureCount, failureReason, failureStrategy) =>
      protobuf.ExceptionState(Some(failureCount), Some(failureReason), Some(ctx.toProto[protobuf.FailureStrategyMessage](failureStrategy)))
    case exceptionStrategy: ExceptionStrategy => exceptionStrategy match {
      case ExceptionStrategy.Fatal => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.FATAL), None)
      case ExceptionStrategy.BlockTransition => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.BLOCK_TRANSITION), None)
      case ExceptionStrategy.Continue(marking, output) => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.CONTINUE), None, markingDataToProto(marking, ctx), Some(ctx.toProtoUnkown(output.asInstanceOf[AnyRef])))
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
    case protobuf.TransitionFiredMessage(Some(jobId), Some(transitionId), correlationId, consumed, produced, Some(state), newJobsIds, Some(output)) =>
      protocol.TransitionFired(jobId, transitionId, correlationId, protoToMarkingData(consumed, ctx),
        protoToMarkingData(produced, ctx), ctx.toDomain[protocol.InstanceState](state), newJobsIds.toSet, ctx.toDomain[Any](output))
    case protobuf.InstanceState(Some(sequenceNr), marking, Some(state), jobs) =>
      val jobMap: Map[Long, protocol.JobState] = jobs.map(ctx.toDomain[protocol.JobState]).map(j => j.id -> j).toMap
      protocol.InstanceState(sequenceNr, protoToMarkingData(marking, ctx), ctx.toDomain[Any](state), jobMap)
    case protobuf.JobState(Some(jobId), Some(transitionId), consumed, Some(input), exceptionState) =>
      protocol.JobState(jobId, transitionId, protoToMarkingData(consumed, ctx), ctx.toDomain[Any](input), exceptionState.map(ctx.toDomain[protocol.ExceptionState]))
    case protobuf.ExceptionState(Some(failureCount), Some(failureReason), Some(strategy)) =>
      protocol.ExceptionState(failureCount, failureReason, ctx.toDomain[ExceptionStrategy](strategy))
    case protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.FATAL), _, _, _) =>
      protocol.ExceptionStrategy.Fatal
    case protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.BLOCK_TRANSITION), _, _, _) =>
      protocol.ExceptionStrategy.BlockTransition
    case protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.RETRY), Some(retryDelay), _, _) =>
      protocol.ExceptionStrategy.RetryWithDelay(retryDelay)
    case protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.CONTINUE), _, marking, Some(output)) =>
      protocol.ExceptionStrategy.Continue(protoToMarkingData(marking, ctx), ctx.toDomain[Any](output))
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
