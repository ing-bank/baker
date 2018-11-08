package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol.ExceptionStrategy
import com.ing.baker.runtime.actor.process_instance.protobuf.FailureStrategyMessage.StrategyTypeMessage
import com.ing.baker.runtime.actor.process_instance.{protobuf, ProcessInstanceProtocol => protocol}
import com.ing.baker.runtime.actor.serialization.{ProtoEventAdapter, ProtoEventAdapterModule}

class ProcessInstanceModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {

    case protocol.GetState =>
      protobuf.GetState()
    case protocol.Stop(delete) =>
      protobuf.Stop(Some(delete))

    case protocol.Initialize(marking, state) =>
      protobuf.Initialize(
        toProtoMarking(marking, ctx),
        Some(ctx.toProtoAny(state.asInstanceOf[AnyRef])))
    case protocol.Initialized(marking, state) =>
        protobuf.InitializedMessage(toProtoMarking(marking, ctx), Some(ctx.toProtoAny(state.asInstanceOf[AnyRef])))
    case protocol.AlreadyInitialized(processId) =>
        protobuf.AlreadyInitialized(Some(processId))
    case protocol.Uninitialized(processId) =>
        protobuf.Uninitialized(Some(processId))

    case protocol.FireTransition(transitionid, input, correlationId) =>
      protobuf.FireTransition(Some(transitionid), Some(ctx.toProtoAny(input.asInstanceOf[AnyRef])), correlationId)
    case protocol.AlreadyReceived(correlationId) =>
      protobuf.AlreadyReceived(Some(correlationId))
    case protocol.TransitionNotEnabled(transitionId, reason) =>
      protobuf.TransitionNotEnabled(Some(transitionId), Some(reason))
    case protocol.TransitionFired(jobId, transitionId, correlationId, consumed, produced, state, newJobs, output) =>
      protobuf.TransitionFiredMessage(Some(jobId), Some(transitionId), correlationId,
        toProtoMarking(consumed, ctx), toProtoMarking(produced, ctx), Some(ctx.toProto[protobuf.InstanceState](state)),
        newJobs.toSeq, Some(ctx.toProtoAny(output.asInstanceOf[AnyRef])))
    case protocol.TransitionFailed(jobId, transitionId, correlationId, consume, input, reason, strategy) =>
      protobuf.TransitionFailedMessage(Some(jobId), Some(transitionId), correlationId, toProtoMarking(consume, ctx),
        Some(ctx.toProtoAny(input.asInstanceOf[AnyRef])), Some(reason), Some(ctx.toProto[protobuf.FailureStrategyMessage](strategy)))

    case protocol.InstanceState(sequenceNr, marking, state, jobs) =>
      protobuf.InstanceState(Some(sequenceNr), toProtoMarking(marking, ctx),
        Some(ctx.toProtoAny(state.asInstanceOf[AnyRef])),
        jobs.values.map(job => ctx.toProto[protobuf.JobState](job)).toSeq)
    case protocol.JobState(jobId, transitionId, consumed, input, exceptionState) =>
      protobuf.JobState(Some(jobId), Some(transitionId), toProtoMarking(consumed, ctx),
        Some(ctx.toProtoAny(input.asInstanceOf[AnyRef])), exceptionState.map(ctx.toProto[protobuf.ExceptionState]))
    case protocol.ExceptionState(failureCount, failureReason, failureStrategy) =>
      protobuf.ExceptionState(Some(failureCount), Some(failureReason), Some(ctx.toProto[protobuf.FailureStrategyMessage](failureStrategy)))
    case exceptionStrategy: ExceptionStrategy => exceptionStrategy match {
      case ExceptionStrategy.Fatal => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.FATAL), None)
      case ExceptionStrategy.BlockTransition => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.BLOCK_TRANSITION), None)
      case ExceptionStrategy.Continue(marking, output) => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.CONTINUE), None, toProtoMarking(marking, ctx), Some(ctx.toProtoAny(output.asInstanceOf[AnyRef])))
      case ExceptionStrategy.RetryWithDelay(delay) => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.RETRY), Some(delay))
    }

    // These 3 messages do not have a domain class, they are directly persisted by the ProcessInstance actor
    case msg: protobuf.TransitionFired => msg
    case msg: protobuf.TransitionFailed => msg
    case msg: protobuf.Initialized => msg
  }

  private def toProtoMarking(markingData: Marking[Id], ctx: ProtoEventAdapter): Seq[protobuf.MarkingData] = {
    markingData.flatMap { case (placeId, multiSet) =>
      if (multiSet.isEmpty)
        throw new IllegalArgumentException(s"Empty marking encoutered for place id: $placeId")

        multiSet.map { case (data, count) =>
          protobuf.MarkingData(Some(placeId), Some(ctx.toProtoAny(data.asInstanceOf[AnyRef])), Some(count))
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
        toDomainMarking(markingData, ctx),
        ctx.toDomain[Any](state))
    case protobuf.InitializedMessage(marking, Some(state)) =>
      protocol.Initialized(toDomainMarking(marking, ctx), ctx.toDomain[Any](state))
    case protobuf.Uninitialized(Some(processId)) =>
      protocol.Uninitialized(processId)
    case protobuf.AlreadyInitialized(Some(processId)) =>
      protocol.AlreadyInitialized(processId)

    case protobuf.FireTransition(Some(transitionId), Some(input), correlationId) =>
      protocol.FireTransition(transitionId, ctx.toDomain[Any](input), correlationId)
    case protobuf.AlreadyReceived(Some(correlationId)) =>
      protocol.AlreadyReceived(correlationId)
    case protobuf.TransitionNotEnabled(Some(transitionId), Some(reason)) =>
      protocol.TransitionNotEnabled(transitionId, reason)
    case protobuf.TransitionFiredMessage(Some(jobId), Some(transitionId), correlationId, consumed, produced, Some(state), newJobsIds, Some(output)) =>
      protocol.TransitionFired(jobId, transitionId, correlationId, toDomainMarking(consumed, ctx),
        toDomainMarking(produced, ctx), ctx.toDomain[protocol.InstanceState](state), newJobsIds.toSet, ctx.toDomain[Any](output))
    case protobuf.TransitionFailedMessage(Some(jobId), Some(transitionId), correlationId, consume, Some(input), Some(reason), Some(strategy)) =>
      protocol.TransitionFailed(jobId, transitionId, correlationId, toDomainMarking(consume, ctx), ctx.toDomain[Any](input), reason, ctx.toDomain[protocol.ExceptionStrategy](strategy))

    case protobuf.InstanceState(Some(sequenceNr), marking, Some(state), jobs) =>
      val jobMap: Map[Long, protocol.JobState] = jobs.map(ctx.toDomain[protocol.JobState]).map(j => j.id -> j).toMap
      protocol.InstanceState(sequenceNr, toDomainMarking(marking, ctx), ctx.toDomain[Any](state), jobMap)
    case protobuf.JobState(Some(jobId), Some(transitionId), consumed, Some(input), exceptionState) =>
      protocol.JobState(jobId, transitionId, toDomainMarking(consumed, ctx), ctx.toDomain[Any](input), exceptionState.map(ctx.toDomain[protocol.ExceptionState]))
    case protobuf.ExceptionState(Some(failureCount), Some(failureReason), Some(strategy)) =>
      protocol.ExceptionState(failureCount, failureReason, ctx.toDomain[ExceptionStrategy](strategy))
    case protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.FATAL), _, _, _) =>
      protocol.ExceptionStrategy.Fatal
    case protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.BLOCK_TRANSITION), _, _, _) =>
      protocol.ExceptionStrategy.BlockTransition
    case protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.RETRY), Some(retryDelay), _, _) =>
      protocol.ExceptionStrategy.RetryWithDelay(retryDelay)
    case protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.CONTINUE), _, marking, Some(output)) =>
      protocol.ExceptionStrategy.Continue(toDomainMarking(marking, ctx), ctx.toDomain[Any](output))

    // These 3 messages do not have a domain class, they are directly persisted by the ProcessInstance actor
    case msg: protobuf.TransitionFired => msg
    case msg: protobuf.TransitionFailed => msg
    case msg: protobuf.Initialized => msg
  }

  private def toDomainMarking(markingData: Seq[protobuf.MarkingData], ctx: ProtoEventAdapter): Marking[Id] = {
    markingData.foldLeft[Marking[Id]](Map.empty) {
      case (acc, protobuf.MarkingData(Some(placeId), Some(data), Some(count))) =>
        val placeData: MultiSet[Any] = acc.get(placeId).getOrElse(MultiSet.empty)
        val deserializedData = ctx.toDomain[Any](data)
        acc + (placeId -> (placeData + (deserializedData -> count)))
      case _ => throw new IllegalStateException("missing data in serialized data when deserializing MarkingData")
    }
  }
}
