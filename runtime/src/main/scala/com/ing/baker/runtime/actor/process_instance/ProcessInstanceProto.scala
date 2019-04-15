package com.ing.baker.runtime.actor.process_instance

import cats.instances.list._
import cats.instances.try_._
import cats.instances.option._
import cats.syntax.traverse._
import com.ing.baker.petrinet.api.{Id, Marking, MultiSet}
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.actor.process_instance.protobuf.FailureStrategyMessage.StrategyTypeMessage
import com.ing.baker.runtime.actortyped.serialization.ProtoMap
import com.ing.baker.runtime.actortyped.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.actortyped.serialization.protomappings.AnyRefMapping.SerializersProvider
import scalapb.GeneratedMessageCompanion

import scala.util.{Failure, Success, Try}

object ProcessInstanceProto {

  implicit def stopProto: ProtoMap[Stop, protobuf.Stop] =
    new ProtoMap[Stop, protobuf.Stop] {

      val companion = protobuf.Stop

      def toProto(a: Stop): protobuf.Stop =
        protobuf.Stop(Some(a.delete))

      def fromProto(message: protobuf.Stop): Try[Stop] =
        for {
          delete <- versioned(message.delete, "delete")
        } yield Stop(delete)
      }

  implicit def getStateProto: ProtoMap[GetState.type , protobuf.GetState] =
    new ProtoMap[GetState.type, protobuf.GetState] {

      val companion = protobuf.GetState

      def toProto(a: GetState.type): protobuf.GetState =
        protobuf.GetState()

      def fromProto(message: protobuf.GetState): Try[GetState.type] =
        Success(GetState)
    }

  implicit def exceptionStrategyProto(implicit ev0: SerializersProvider): ProtoMap[ExceptionStrategy, protobuf.FailureStrategyMessage] =
    new ProtoMap[ExceptionStrategy, protobuf.FailureStrategyMessage] {

      val companion: GeneratedMessageCompanion[protobuf.FailureStrategyMessage] =
        protobuf.FailureStrategyMessage

      override def toProto(a: ExceptionStrategy): protobuf.FailureStrategyMessage =
        a match {
          case ExceptionStrategy.BlockTransition => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.BLOCK_TRANSITION), None)
          case ExceptionStrategy.Continue(marking, output) => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.CONTINUE), None, toProtoMarking(marking), Some(ctxToProto(output.asInstanceOf[AnyRef])))
          case ExceptionStrategy.RetryWithDelay(delay) => protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.RETRY), Some(delay))
        }

      override def fromProto(message: protobuf.FailureStrategyMessage): Try[ExceptionStrategy] =
        message match {
          case protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.BLOCK_TRANSITION), _, _, _) =>
            Success(ExceptionStrategy.BlockTransition)
          case protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.RETRY), Some(retryDelay), _, _) =>
            Success(ExceptionStrategy.RetryWithDelay(retryDelay))
          case protobuf.FailureStrategyMessage(Some(StrategyTypeMessage.CONTINUE), _, marking, Some(output)) =>
            toDomainMarking(marking).map(ExceptionStrategy.Continue(_, ctxFromProto(output)))
          case _ =>
            Failure(new IllegalStateException("Got a protobuf.FailureStrategyMessage with an unrecognized StrategyTypeMessage"))
        }
    }

  implicit def exceptionStateProto(implicit ev0: SerializersProvider): ProtoMap[ExceptionState, protobuf.ExceptionState] =
    new ProtoMap[ExceptionState, protobuf.ExceptionState] {

      val companion: GeneratedMessageCompanion[protobuf.ExceptionState] =
        protobuf.ExceptionState

      override def toProto(a: ExceptionState): protobuf.ExceptionState =
        protobuf.ExceptionState(Some(a.failureCount), Some(a.failureReason), Some(ctxToProto(a.failureStrategy)))

      override def fromProto(message: protobuf.ExceptionState): Try[ExceptionState] =
        for {
          failureCount <- versioned(message.failureCount, "failureCount")
          failureReason <- versioned(message.failureReason, "failureReason")
          exceptionStrategyProtoM <- versioned(message.failureStrategy, "failureStrategy")
          exceptionStrategy <- ctxFromProto(exceptionStrategyProtoM)(exceptionStrategyProto)
        } yield ExceptionState(failureCount, failureReason, exceptionStrategy)
    }

  implicit def jobStateProto(implicit ev0: SerializersProvider): ProtoMap[JobState, protobuf.JobState] =
    new ProtoMap[JobState, protobuf.JobState] {

      val companion: GeneratedMessageCompanion[protobuf.JobState] =
        protobuf.JobState

      override def toProto(a: JobState): protobuf.JobState =
        protobuf.JobState(Some(a.id), Some(a.transitionId), toProtoMarking(a.consumedMarking),
          Some(ctxToProto(a.input.asInstanceOf[AnyRef])), a.exceptionState.map(ctxToProto(_)))

      override def fromProto(message: protobuf.JobState): Try[JobState] =
        for {
          jobId <- versioned(message.jobId, "jobid")
          transitionId <- versioned(message.transitionId, "transitionId")
          inputProto <- versioned(message.input, "input")
          consumed <- toDomainMarking(message.consumedMarking)
          input <- ctxFromProto(inputProto)
          exceptionState <- message.exceptionState.traverse(ctxFromProto(_))
        } yield JobState(jobId, transitionId, consumed, input, exceptionState)
    }

  implicit def instanceStateProto(implicit ev0: SerializersProvider): ProtoMap[InstanceState, protobuf.InstanceState] =
    new ProtoMap[InstanceState, protobuf.InstanceState] {

      val companion = protobuf.InstanceState

      def toProto(a: InstanceState): protobuf.InstanceState =
        protobuf.InstanceState(Some(a.sequenceNr), toProtoMarking(a.marking),
          Some(ctxToProto(a.state.asInstanceOf[AnyRef])),
          a.jobs.values.map(job => ctxToProto(job)).toSeq)

      def fromProto(message: protobuf.InstanceState): Try[InstanceState] =
        for {
          sequenceNr <- versioned(message.sequenceNr, "sequenceNr")
          marking <- toDomainMarking(message.marking)
          stateProto <- versioned(message.state, "state")
          state <- ctxFromProto(stateProto)
          jobList <- message.jobs.toList.traverse(ctxFromProto(_))
          jobMap = jobList.map(j => j.id -> j).toMap
        } yield InstanceState(sequenceNr, marking, state, jobMap)
    }

  implicit def initializeProto(implicit ev0: SerializersProvider): ProtoMap[Initialize, protobuf.Initialize] =
    new ProtoMap[Initialize, protobuf.Initialize] {

      val companion: GeneratedMessageCompanion[protobuf.Initialize] =
        protobuf.Initialize

      override def toProto(a: Initialize): protobuf.Initialize =
        protobuf.Initialize(toProtoMarking(a.marking), Some(ctxToProto(a.state.asInstanceOf[AnyRef])))

      override def fromProto(message: protobuf.Initialize): Try[Initialize] =
        for {
          state <- versioned(message.state, "state")
          marking <- toDomainMarking(message.markingData)
        } yield Initialize(marking, state)
    }

   implicit def initializedProto(implicit ev0: SerializersProvider): ProtoMap[Initialized, protobuf.InitializedMessage] =
    new ProtoMap[Initialized, protobuf.InitializedMessage] {

      val companion: GeneratedMessageCompanion[protobuf.InitializedMessage] =
        protobuf.InitializedMessage

      override def toProto(a: Initialized): protobuf.InitializedMessage =
        protobuf.InitializedMessage(toProtoMarking(a.marking), Some(ctxToProto(a.state.asInstanceOf[AnyRef])))

      override def fromProto(message: protobuf.InitializedMessage): Try[Initialized] =
        for {
          state <- versioned(message.state, "state")
          marking <- toDomainMarking(message.marking)
        } yield Initialized(marking, state)
    }

  implicit def uninitializedProto(implicit ev0: SerializersProvider): ProtoMap[Uninitialized, protobuf.Uninitialized] =
    new ProtoMap[Uninitialized, protobuf.Uninitialized] {

      val companion: GeneratedMessageCompanion[protobuf.Uninitialized] =
        protobuf.Uninitialized

      override def toProto(a: Uninitialized): protobuf.Uninitialized =
        protobuf.Uninitialized(Some(a.processId))

      override def fromProto(message: protobuf.Uninitialized): Try[Uninitialized] =
        versioned(message.processId, "processId").map(Uninitialized)
    }

  implicit def alreadyInitializedProto(implicit ev0: SerializersProvider): ProtoMap[AlreadyInitialized, protobuf.AlreadyInitialized] =
    new ProtoMap[AlreadyInitialized, protobuf.AlreadyInitialized] {

      val companion: GeneratedMessageCompanion[protobuf.AlreadyInitialized] =
        protobuf.AlreadyInitialized

      override def toProto(a: AlreadyInitialized): protobuf.AlreadyInitialized =
        protobuf.AlreadyInitialized(Some(a.processId))

      override def fromProto(message: protobuf.AlreadyInitialized): Try[AlreadyInitialized] =
        versioned(message.processId, "processId").map(AlreadyInitialized)
    }

  private def toDomainMarking(markingData: Seq[protobuf.MarkingData])(implicit ev0: SerializersProvider): Try[Marking[Id]] = {
    markingData.foldLeft[Try[Marking[Id]]](Success(Map.empty)) {
      case (accTry, protobuf.MarkingData(Some(placeId), Some(data), Some(count))) =>
        accTry.map { acc =>
          val placeData: MultiSet[Any] = acc.getOrElse(placeId, MultiSet.empty)
          val deserializedData = ctxFromProto(data)
          acc + (placeId -> (placeData + (deserializedData -> count)))
        }
      case _ =>
        Failure(new IllegalStateException("missing data in serialized data when deserializing MarkingData"))
    }
  }

  private def toProtoMarking(markingData: Marking[Id])(implicit ev0: SerializersProvider): Seq[protobuf.MarkingData] = {
    markingData.flatMap { case (placeId, multiSet) =>
      if (multiSet.isEmpty)
        throw new IllegalArgumentException(s"Empty marking encoutered for place id: $placeId")
      multiSet.map { case (data, count) =>
        protobuf.MarkingData(Some(placeId), Some(ctxToProto(data.asInstanceOf[AnyRef])), Some(count))
      }
    }.toSeq
  }

}
