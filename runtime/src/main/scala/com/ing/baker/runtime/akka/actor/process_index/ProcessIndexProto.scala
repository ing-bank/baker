package com.ing.baker.runtime.akka.actor.process_index

import java.util.concurrent.TimeUnit

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.runtime.akka.actor.ClusterBakerActorProvider.GetShardIndex
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex._
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.FireSensoryEventReaction.{NotifyBoth, NotifyWhenCompleted, NotifyWhenReceived}
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.akka.actor.serialization.{ProtoMap, SerializersProvider}

import scala.concurrent.duration.FiniteDuration
import scala.util.{Failure, Success, Try}

object ProcessIndexProto {

  implicit def getShardIndexProto: ProtoMap[GetShardIndex, protobuf.GetShardIndex] =
    new ProtoMap[GetShardIndex, protobuf.GetShardIndex] {

      val companion = protobuf.GetShardIndex

      def toProto(a: GetShardIndex): protobuf.GetShardIndex =
        protobuf.GetShardIndex(Some(a.entityId))

      def fromProto(message: protobuf.GetShardIndex): Try[GetShardIndex] =
        for {
          entityId <- versioned(message.entityId, "entityId")
        } yield GetShardIndex(entityId)
    }

  implicit def actorCreatedProto: ProtoMap[ActorCreated, protobuf.ActorCreated] =
    new ProtoMap[ActorCreated, protobuf.ActorCreated] {

      val companion = protobuf.ActorCreated

      def toProto(a: ActorCreated): protobuf.ActorCreated =
        protobuf.ActorCreated(Some(a.recipeId), Some(a.processId), Some(a.createdDateTime))

      def fromProto(message: protobuf.ActorCreated): Try[ActorCreated] =
        for {
          recipeId <- versioned(message.recipeId, "recipeId")
          processId <- versioned(message.processId, "processId")
          createdDateTime <- versioned(message.dateCreated, "dateCreated")
        } yield ActorCreated(recipeId, processId, createdDateTime)
    }

  implicit def actorDeletedProto: ProtoMap[ActorDeleted, protobuf.ActorDeleted] =
    new ProtoMap[ActorDeleted, protobuf.ActorDeleted] {

      val companion = protobuf.ActorDeleted

      def toProto(a: ActorDeleted): protobuf.ActorDeleted =
        protobuf.ActorDeleted(Some(a.processId))

      def fromProto(message: protobuf.ActorDeleted): Try[ActorDeleted] =
        for {
          processId <- versioned(message.processId, "processId")
        } yield ActorDeleted(processId)
    }

  implicit def actorPassivatedProto: ProtoMap[ActorPassivated, protobuf.ActorPassivated] =
    new ProtoMap[ActorPassivated, protobuf.ActorPassivated] {

      val companion = protobuf.ActorPassivated

      def toProto(a: ActorPassivated): protobuf.ActorPassivated =
        protobuf.ActorPassivated(Some(a.processId))

      def fromProto(message: protobuf.ActorPassivated): Try[ActorPassivated] =
        for {
          processId <- versioned(message.processId, "processId")
        } yield ActorPassivated(processId)
    }

  implicit def actorActivatedProto: ProtoMap[ActorActivated, protobuf.ActorActivated] =
    new ProtoMap[ActorActivated, protobuf.ActorActivated] {

      val companion = protobuf.ActorActivated

      def toProto(a: ActorActivated): protobuf.ActorActivated =
        protobuf.ActorActivated(Some(a.processId))

      def fromProto(message: protobuf.ActorActivated): Try[ActorActivated] =
        for {
          processId <- versioned(message.processId, "processId")
        } yield ActorActivated(processId)
    }

  implicit def actorMetadataProto: ProtoMap[ActorMetadata, protobuf.ActorMetaData] =
    new ProtoMap[ActorMetadata, protobuf.ActorMetaData] {

      val companion = protobuf.ActorMetaData

      def toProto(a: ActorMetadata): protobuf.ActorMetaData =
        protobuf.ActorMetaData(
          Some(a.recipeId),
          Some(a.processId),
          Some(a.createdDateTime),
          Some(a.processStatus == ProcessIndex.Deleted)
        )

      def fromProto(message: protobuf.ActorMetaData): Try[ActorMetadata] =
        for {
          recipeId <- versioned(message.recipeId, "recipeId")
          processId <- versioned(message.processId, "processId")
          createdDateTime <- versioned(message.createdTime, "createdTime")
          isDeleted <- versioned(message.isDeleted, "createdTime")
          processStatus = if (isDeleted) ProcessIndex.Deleted else ProcessIndex.Active
        } yield ActorMetadata(recipeId, processId, createdDateTime, processStatus)
    }

  implicit def getIndexProto: ProtoMap[GetIndex.type, protobuf.GetIndex] =
    new ProtoMap[GetIndex.type, protobuf.GetIndex] {

      val companion = protobuf.GetIndex

      def toProto(a: GetIndex.type): protobuf.GetIndex =
        protobuf.GetIndex()

      def fromProto(message: protobuf.GetIndex): Try[GetIndex.type] =
        Success(GetIndex)
    }

  implicit def indexProto: ProtoMap[Index, protobuf.Index] =
    new ProtoMap[Index, protobuf.Index] {

      val companion = protobuf.Index

      def toProto(a: Index): protobuf.Index =
        protobuf.Index(a.entries.map { e =>
          protobuf.ActorMetaData(
            Some(e.recipeId),
            Some(e.processId),
            Some(e.createdDateTime),
            Some(e.processStatus == ProcessIndex.Deleted)
          )
        })

      def fromProto(message: protobuf.Index): Try[Index] =
        for {
          entries <- message.entries.toList.traverse[Try, ActorMetadata] { e =>
            for {
              recipeId <- versioned(e.recipeId, "recipeId")
              processId <- versioned(e.processId, "processId")
              createdDateTime <- versioned(e.createdTime, "createdTime")
              isDeleted <- versioned(e.isDeleted, "createdTime")
              processStatus = if (isDeleted) ProcessIndex.Deleted else ProcessIndex.Active
            } yield ActorMetadata(recipeId, processId, createdDateTime, processStatus)
          }
        } yield Index(entries)
    }

  implicit def createProcessProto: ProtoMap[CreateProcess, protobuf.CreateProcess] =
    new ProtoMap[CreateProcess, protobuf.CreateProcess] {

      val companion = protobuf.CreateProcess

      def toProto(a: CreateProcess): protobuf.CreateProcess =
        protobuf.CreateProcess(Some(a.recipeId), Some(a.processId))

      def fromProto(message: protobuf.CreateProcess): Try[CreateProcess] =
        for {
          recipeId <- versioned(message.recipeId, "recipeId")
          processId <- versioned(message.processId, "processId")
        } yield CreateProcess(recipeId, processId)
    }

  implicit def processEventProto(implicit provider: SerializersProvider): ProtoMap[ProcessEvent, protobuf.ProcessEvent] =
    new ProtoMap[ProcessEvent, protobuf.ProcessEvent] {

      val companion = protobuf.ProcessEvent

      def toProto(a: ProcessEvent): protobuf.ProcessEvent =
        protobuf.ProcessEvent(
          Some(a.processId),
          Some(ctxToProto(a.event)),
          a.correlationId,
          Some(a.timeout.toMillis),
          Some(a.reaction match {
            case FireSensoryEventReaction.NotifyWhenReceived =>
              protobuf.FireSensoryEventReaction(
                protobuf.FireSensoryEventReaction.SealedValue.Received(protobuf.NotifyWhenReceived()))
            case FireSensoryEventReaction.NotifyWhenCompleted(waitForRetries) =>
              protobuf.FireSensoryEventReaction(
                protobuf.FireSensoryEventReaction.SealedValue.Completed(protobuf.NotifyWhenCompleted(Some(waitForRetries))))
            case FireSensoryEventReaction.NotifyBoth(waitForRetries, receiver) =>
              protobuf.FireSensoryEventReaction(
                protobuf.FireSensoryEventReaction.SealedValue.Both(protobuf.NotifyBoth(Some(waitForRetries), Some(ctxToProto(receiver)))))
          })
        )

      def fromProto(message: protobuf.ProcessEvent): Try[ProcessEvent] =
        for {
          processId <- versioned(message.processId, "processId")
          eventProto <- versioned(message.event, "event")
          timeout <- versioned(message.timeout, "timeout")
          reactionProto <- versioned(message.reaction, "reaction")
          event <- ctxFromProto(eventProto)
          reaction <- reactionProto.sealedValue match {
            case protobuf.FireSensoryEventReaction.SealedValue.Received(_) =>
              Success(NotifyWhenReceived)
            case protobuf.FireSensoryEventReaction.SealedValue.Completed(protobuf.NotifyWhenCompleted(waitForRetries)) =>
              versioned(waitForRetries, "waitForRetries").map(NotifyWhenCompleted.apply)
            case protobuf.FireSensoryEventReaction.SealedValue.Both(protobuf.NotifyBoth(waitForRetriesProto, receiverProto)) =>
              for {
                waitForRetries <- versioned(waitForRetriesProto, "waitForRetries")
                receiverProto <- versioned(receiverProto, "receiver")
                receiver <- ctxFromProto(receiverProto)
              } yield NotifyBoth(waitForRetries, receiver)
            case protobuf.FireSensoryEventReaction.SealedValue.Empty =>
              Failure(new IllegalStateException("Received Empty of the oneof FireSensoryEventReaction protocol message."))
          }
          time = FiniteDuration(timeout, TimeUnit.MILLISECONDS)
        } yield ProcessEvent(processId, event, message.correlationId, time, reaction)
    }

  implicit def retryBlockedInteractionProto: ProtoMap[RetryBlockedInteraction, protobuf.RetryBlockedInteraction] =
    new ProtoMap[RetryBlockedInteraction, protobuf.RetryBlockedInteraction] {

      val companion = protobuf.RetryBlockedInteraction

      def toProto(a: RetryBlockedInteraction): protobuf.RetryBlockedInteraction =
        protobuf.RetryBlockedInteraction(Some(a.processId), Some(a.interactionName))

      def fromProto(message: protobuf.RetryBlockedInteraction): Try[RetryBlockedInteraction] =
        for {
          processId <- versioned(message.processId, "processId")
          interactionName <- versioned(message.interactionName, "interactionName")
        } yield RetryBlockedInteraction(processId, interactionName)
    }

  implicit def resolveBlockedInteractionProto: ProtoMap[ResolveBlockedInteraction, protobuf.ResolveBlockedInteraction] =
    new ProtoMap[ResolveBlockedInteraction, protobuf.ResolveBlockedInteraction] {

      val companion = protobuf.ResolveBlockedInteraction

      def toProto(a: ResolveBlockedInteraction): protobuf.ResolveBlockedInteraction =
        protobuf.ResolveBlockedInteraction(Some(a.processId), Some(a.interactionName), Some(ctxToProto(a.output)))

      def fromProto(message: protobuf.ResolveBlockedInteraction): Try[ResolveBlockedInteraction] =
        for {
          processId <- versioned(message.processId, "processId")
          interactionName <- versioned(message.interactionName, "interactionName")
          eventProto <- versioned(message.event, "event")
          event <- ctxFromProto(eventProto)
        } yield ResolveBlockedInteraction(processId, interactionName, event)
    }

  implicit def stopRetryingInteractionProto: ProtoMap[StopRetryingInteraction, protobuf.StopRetryingInteraction] =
    new ProtoMap[StopRetryingInteraction, protobuf.StopRetryingInteraction] {

      val companion = protobuf.StopRetryingInteraction

      def toProto(a: StopRetryingInteraction): protobuf.StopRetryingInteraction =
        protobuf.StopRetryingInteraction(Some(a.processId), Some(a.interactionName))

      def fromProto(message: protobuf.StopRetryingInteraction): Try[StopRetryingInteraction] =
        for {
          processId <- versioned(message.processId, "processId")
          interactionName <- versioned(message.interactionName, "interactionName")
        } yield StopRetryingInteraction(processId, interactionName)
    }

  implicit def processEventResponseProto(implicit provider: SerializersProvider): ProtoMap[ProcessEventResponse, protobuf.ProcessEventResponse] =
    new ProtoMap[ProcessEventResponse, protobuf.ProcessEventResponse] {

      val companion = protobuf.ProcessEventResponse

      def toProto(a: ProcessEventResponse): protobuf.ProcessEventResponse =
        protobuf.ProcessEventResponse(Some(a.processId), None)

      def fromProto(message: protobuf.ProcessEventResponse): Try[ProcessEventResponse] =
        for {
          processId <- versioned(message.processId, "processId")
        } yield ProcessEventResponse(processId)
    }

  implicit def getProcessStateProto: ProtoMap[GetProcessState, protobuf.GetProcessState] =
    new ProtoMap[GetProcessState, protobuf.GetProcessState] {

      val companion = protobuf.GetProcessState

      def toProto(a: GetProcessState): protobuf.GetProcessState =
        protobuf.GetProcessState(Some(a.processId))

      def fromProto(message: protobuf.GetProcessState): Try[GetProcessState] =
        for {
          processId <- versioned(message.processId, "processId")
        } yield GetProcessState(processId)
    }

  implicit def getCompiledRecipeProto: ProtoMap[GetCompiledRecipe, protobuf.GetCompiledRecipe] =
    new ProtoMap[GetCompiledRecipe, protobuf.GetCompiledRecipe] {

      val companion = protobuf.GetCompiledRecipe

      def toProto(a: GetCompiledRecipe): protobuf.GetCompiledRecipe =
        protobuf.GetCompiledRecipe(Some(a.processId))

      def fromProto(message: protobuf.GetCompiledRecipe): Try[GetCompiledRecipe] =
        for {
          processId <- versioned(message.recipeId, "recipeId")
        } yield GetCompiledRecipe(processId)
    }

  implicit def receivePeriodExpiredProtoSERejection: ProtoMap[FireSensoryEventRejection.ReceivePeriodExpired, protobuf.ReceivePeriodExpired] =
    new ProtoMap[FireSensoryEventRejection.ReceivePeriodExpired, protobuf.ReceivePeriodExpired] {

      val companion = protobuf.ReceivePeriodExpired

      def toProto(a: FireSensoryEventRejection.ReceivePeriodExpired): protobuf.ReceivePeriodExpired =
        protobuf.ReceivePeriodExpired(Some(a.processId))

      def fromProto(message: protobuf.ReceivePeriodExpired): Try[FireSensoryEventRejection.ReceivePeriodExpired] =
        for {
          processId <- versioned(message.processId, "processId")
        } yield FireSensoryEventRejection.ReceivePeriodExpired(processId)
    }

  implicit def invalidEventProtoSERejection: ProtoMap[FireSensoryEventRejection.InvalidEvent, protobuf.InvalidEvent] =
    new ProtoMap[FireSensoryEventRejection.InvalidEvent, protobuf.InvalidEvent] {

      val companion = protobuf.InvalidEvent

      def toProto(a: FireSensoryEventRejection.InvalidEvent): protobuf.InvalidEvent =
        protobuf.InvalidEvent(Some(a.processId), Some(a.msg))

      def fromProto(message: protobuf.InvalidEvent): Try[FireSensoryEventRejection.InvalidEvent] =
        for {
          processId <- versioned(message.processId, "processId")
          msg <- versioned(message.reason, "reason")
        } yield FireSensoryEventRejection.InvalidEvent(processId, msg)
    }

  implicit def processDeletedProto: ProtoMap[ProcessDeleted, protobuf.ProcessDeleted] =
    new ProtoMap[ProcessDeleted, protobuf.ProcessDeleted] {

      val companion = protobuf.ProcessDeleted

      def toProto(a: ProcessDeleted): protobuf.ProcessDeleted =
        protobuf.ProcessDeleted(Some(a.processId))

      def fromProto(message: protobuf.ProcessDeleted): Try[ProcessDeleted] =
        for {
          processId <- versioned(message.processId, "processId")
        } yield ProcessDeleted(processId)
    }

  implicit def processDeletedProtoSERejection: ProtoMap[FireSensoryEventRejection.ProcessDeleted, protobuf.ProcessDeleted] =
    new ProtoMap[FireSensoryEventRejection.ProcessDeleted, protobuf.ProcessDeleted] {

      val companion = protobuf.ProcessDeleted

      def toProto(a: FireSensoryEventRejection.ProcessDeleted): protobuf.ProcessDeleted =
        protobuf.ProcessDeleted(Some(a.processId))

      def fromProto(message: protobuf.ProcessDeleted): Try[FireSensoryEventRejection.ProcessDeleted] =
        for {
          processId <- versioned(message.processId, "processId")
        } yield FireSensoryEventRejection.ProcessDeleted(processId)
    }

  implicit def noSuchProcessProtoSERejection: ProtoMap[FireSensoryEventRejection.NoSuchProcess, protobuf.NoSuchProcess] =
    new ProtoMap[FireSensoryEventRejection.NoSuchProcess, protobuf.NoSuchProcess] {

      val companion = protobuf.NoSuchProcess

      def toProto(a: FireSensoryEventRejection.NoSuchProcess): protobuf.NoSuchProcess =
        protobuf.NoSuchProcess(Some(a.processId))

      def fromProto(message: protobuf.NoSuchProcess): Try[FireSensoryEventRejection.NoSuchProcess] =
        for {
          processId <- versioned(message.processId, "processId")
        } yield FireSensoryEventRejection.NoSuchProcess(processId)
    }

  implicit def firingLimitMetProtoSERejection: ProtoMap[FireSensoryEventRejection.FiringLimitMet, protobuf.FiringLimitMet] =
    new ProtoMap[FireSensoryEventRejection.FiringLimitMet, protobuf.FiringLimitMet] {

      val companion = protobuf.FiringLimitMet

      def toProto(a: FireSensoryEventRejection.FiringLimitMet): protobuf.FiringLimitMet =
        protobuf.FiringLimitMet(Some(a.processId))

      def fromProto(message: protobuf.FiringLimitMet): Try[FireSensoryEventRejection.FiringLimitMet] =
        for {
          processId <- versioned(message.processId, "processId")
        } yield FireSensoryEventRejection.FiringLimitMet(processId)
    }


  implicit def alreadyReceivedProtoSERejection: ProtoMap[FireSensoryEventRejection.AlreadyReceived, protobuf.SensoryEventAlreadyReceived] =
    new ProtoMap[FireSensoryEventRejection.AlreadyReceived, protobuf.SensoryEventAlreadyReceived] {

      val companion = protobuf.SensoryEventAlreadyReceived

      def toProto(a: FireSensoryEventRejection.AlreadyReceived): protobuf.SensoryEventAlreadyReceived =
        protobuf.SensoryEventAlreadyReceived(Some(a.processId), Some(a.correlationId))

      def fromProto(message: protobuf.SensoryEventAlreadyReceived): Try[FireSensoryEventRejection.AlreadyReceived] =
        for {
          processId <- versioned(message.processId, "processId")
          correlationId <- versioned(message.correlationId, "correlationId")
        } yield FireSensoryEventRejection.AlreadyReceived(processId, correlationId)
    }


  implicit def noSuchProcessProto: ProtoMap[NoSuchProcess, protobuf.NoSuchProcess] =
    new ProtoMap[NoSuchProcess, protobuf.NoSuchProcess] {

      val companion = protobuf.NoSuchProcess

      def toProto(a: NoSuchProcess): protobuf.NoSuchProcess =
        protobuf.NoSuchProcess(Some(a.processId))

      def fromProto(message: protobuf.NoSuchProcess): Try[NoSuchProcess] =
        for {
          processId <- versioned(message.processId, "processId")
        } yield NoSuchProcess(processId)
    }

  implicit def processAlreadyExistsProto: ProtoMap[ProcessAlreadyExists, protobuf.ProcessAlreadyExists] =
    new ProtoMap[ProcessAlreadyExists, protobuf.ProcessAlreadyExists] {

      val companion = protobuf.ProcessAlreadyExists

      def toProto(a: ProcessAlreadyExists): protobuf.ProcessAlreadyExists =
        protobuf.ProcessAlreadyExists(Some(a.processId))

      def fromProto(message: protobuf.ProcessAlreadyExists): Try[ProcessAlreadyExists] =
        for {
          processId <- versioned(message.processId, "processId")
        } yield ProcessAlreadyExists(processId)
    }

}
