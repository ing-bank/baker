package com.ing.baker.runtime.akka.actor.process_index

import akka.actor.{ActorRef, ActorRefProvider}
import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.runtime.akka.actor.ClusterBakerActorProvider.GetShardIndex
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex._
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.FireSensoryEventReaction.{NotifyBoth, NotifyOnEvent, NotifyWhenCompleted, NotifyWhenReceived}
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.akka.actor.process_index.protobuf.{ActorMetaData, ActorRefId}
import com.ing.baker.runtime.akka.actor.serialization.AkkaSerializerProvider
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.baker.runtime.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned, versionedOptional}
import com.ing.baker.runtime.serialization.protomappings.SensoryEventStatusMappingHelper

import java.util.concurrent.TimeUnit
import scala.concurrent.duration.FiniteDuration
import scala.util.{Failure, Success, Try}

object ProcessIndexProto {

  implicit def akkaActorRefMapping(implicit ev0: ActorRefProvider): ProtoMap[ActorRef, protobuf.ActorRefId] =
    new ProtoMap[ActorRef, protobuf.ActorRefId] {

      val companion = protobuf.ActorRefId

      override def toProto(a: ActorRef): protobuf.ActorRefId =
        protobuf.ActorRefId(Some(akka.serialization.Serialization.serializedActorPath(a)))

      override def fromProto(message: ActorRefId): Try[ActorRef] =
        for {
          identifier <- versioned(message.identifier, "identifier")
          actorRef <- Try(ev0.resolveActorRef(identifier))
        } yield actorRef
    }

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
        protobuf.ActorCreated(Some(a.recipeId), Some(a.recipeInstanceId), Some(a.createdDateTime))

      def fromProto(message: protobuf.ActorCreated): Try[ActorCreated] =
        for {
          recipeId <- versioned(message.recipeId, "recipeId")
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
          createdDateTime <- versioned(message.dateCreated, "dateCreated")
        } yield ActorCreated(recipeId, recipeInstanceId, createdDateTime)
    }

  implicit def actorDeletedProto: ProtoMap[ActorDeleted, protobuf.ActorDeleted] =
    new ProtoMap[ActorDeleted, protobuf.ActorDeleted] {

      val companion = protobuf.ActorDeleted

      def toProto(a: ActorDeleted): protobuf.ActorDeleted =
        protobuf.ActorDeleted(Some(a.recipeInstanceId))

      def fromProto(message: protobuf.ActorDeleted): Try[ActorDeleted] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        } yield ActorDeleted(recipeInstanceId)
    }

  implicit def actorPassivatedProto: ProtoMap[ActorPassivated, protobuf.ActorPassivated] =
    new ProtoMap[ActorPassivated, protobuf.ActorPassivated] {

      val companion = protobuf.ActorPassivated

      def toProto(a: ActorPassivated): protobuf.ActorPassivated =
        protobuf.ActorPassivated(Some(a.recipeInstanceId))

      def fromProto(message: protobuf.ActorPassivated): Try[ActorPassivated] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        } yield ActorPassivated(recipeInstanceId)
    }

  implicit def actorActivatedProto: ProtoMap[ActorActivated, protobuf.ActorActivated] =
    new ProtoMap[ActorActivated, protobuf.ActorActivated] {

      val companion = protobuf.ActorActivated

      def toProto(a: ActorActivated): protobuf.ActorActivated =
        protobuf.ActorActivated(Some(a.recipeInstanceId))

      def fromProto(message: protobuf.ActorActivated): Try[ActorActivated] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        } yield ActorActivated(recipeInstanceId)
    }

  implicit def processIndexSnapShotProto: ProtoMap[ProcessIndexSnapShot, protobuf.ProcessIndexSnapShot] =
    new ProtoMap[ProcessIndexSnapShot, protobuf.ProcessIndexSnapShot] {

      val companion = protobuf.ProcessIndexSnapShot

      override def toProto(processIndexSnapShot: ProcessIndexSnapShot): protobuf.ProcessIndexSnapShot =
        protobuf.ProcessIndexSnapShot(processIndexSnapShot.index.map(entry => entry._1 -> ctxToProto(entry._2)))

      override def fromProto(message: protobuf.ProcessIndexSnapShot): Try[ProcessIndexSnapShot] = {
        Try {
          ProcessIndexSnapShot(message.index.map(entry => entry._1 -> ctxFromProto(entry._2).get))
        }
      }
    }

  implicit def actorMetadataProto: ProtoMap[ActorMetadata, protobuf.ActorMetaData] =
    new ProtoMap[ActorMetadata, protobuf.ActorMetaData] {

      val companion = protobuf.ActorMetaData

      def toProto(a: ActorMetadata): protobuf.ActorMetaData =
        protobuf.ActorMetaData(
          Some(a.recipeId),
          Some(a.recipeInstanceId),
          Some(a.createdDateTime),
          Some(a.processStatus == ProcessIndex.Deleted),
          Some(a.processStatus == ProcessIndex.Passivated)
        )

      def fromProto(message: protobuf.ActorMetaData): Try[ActorMetadata] =
        for {
          recipeId <- versioned(message.recipeId, "recipeId")
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
          createdDateTime <- versioned(message.createdTime, "createdTime")
          isDeleted <- versioned(message.isDeleted, "createdTime")
          isPassivated = versionedOptional(message.isPassivated, false)
          processStatus = readStatus(isDeleted, isPassivated)
        } yield ActorMetadata(recipeId, recipeInstanceId, createdDateTime, processStatus)

      private def readStatus(isDeleted: Boolean, isPassivated: Boolean): ProcessStatus = {
        if (isDeleted) ProcessIndex.Deleted
        else if (isPassivated) ProcessIndex.Passivated
        else ProcessIndex.Active
      }
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
            Some(e.recipeInstanceId),
            Some(e.createdDateTime),
            Some(e.processStatus == ProcessIndex.Deleted)
          )
        })

      def fromProto(message: protobuf.Index): Try[Index] =
        for {
          entries <- message.entries.toList.traverse[Try, ActorMetadata] { e =>
            for {
              recipeId <- versioned(e.recipeId, "recipeId")
              recipeInstanceId <- versioned(e.recipeInstanceId, "RecipeInstanceId")
              createdDateTime <- versioned(e.createdTime, "createdTime")
              isDeleted <- versioned(e.isDeleted, "createdTime")
              processStatus = if (isDeleted) ProcessIndex.Deleted else ProcessIndex.Active
            } yield ActorMetadata(recipeId, recipeInstanceId, createdDateTime, processStatus)
          }
        } yield Index(entries)
    }

  implicit def createProcessProto: ProtoMap[CreateProcess, protobuf.CreateProcess] =
    new ProtoMap[CreateProcess, protobuf.CreateProcess] {

      val companion = protobuf.CreateProcess

      def toProto(a: CreateProcess): protobuf.CreateProcess =
        protobuf.CreateProcess(Some(a.recipeId), Some(a.recipeInstanceId))

      def fromProto(message: protobuf.CreateProcess): Try[CreateProcess] =
        for {
          recipeId <- versioned(message.recipeId, "recipeId")
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        } yield CreateProcess(recipeId, recipeInstanceId)
    }

  implicit def processEventProto(implicit actorRefProvider: ActorRefProvider): ProtoMap[ProcessEvent, protobuf.ProcessEvent] =
    new ProtoMap[ProcessEvent, protobuf.ProcessEvent] {

      val companion = protobuf.ProcessEvent

      def toProto(a: ProcessEvent): protobuf.ProcessEvent =
        protobuf.ProcessEvent(
          Some(a.recipeInstanceId),
          Some(ctxToProto(a.event)),
          a.correlationId,
          Some(a.timeout.toMillis),
          (a.reaction match {
            case FireSensoryEventReaction.NotifyWhenReceived =>
              protobuf.FireSensoryEventReactionMessage(
                protobuf.FireSensoryEventReactionMessage.SealedValue.Received(protobuf.NotifyWhenReceived()))
            case FireSensoryEventReaction.NotifyWhenCompleted(waitForRetries) =>
              protobuf.FireSensoryEventReactionMessage(
                protobuf.FireSensoryEventReactionMessage.SealedValue.Completed(protobuf.NotifyWhenCompleted(Some(waitForRetries))))
            case FireSensoryEventReaction.NotifyBoth(waitForRetries, receiver) =>
              protobuf.FireSensoryEventReactionMessage(
                protobuf.FireSensoryEventReactionMessage.SealedValue.Both(protobuf.NotifyBoth(Some(waitForRetries), Some(ctxToProto(receiver)))))
            case FireSensoryEventReaction.NotifyOnEvent(waitForRetries, onEvent) =>
              protobuf.FireSensoryEventReactionMessage(
                protobuf.FireSensoryEventReactionMessage.SealedValue.OnEvent(protobuf.NotifyOnEvent(Some(waitForRetries), Some(onEvent))))
          }).toFireSensoryEventReaction
        )

      def fromProto(message: protobuf.ProcessEvent): Try[ProcessEvent] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
          eventProto <- versioned(message.event, "event")
          timeout <- versioned(message.timeout, "timeout")
          reactionProto = message.reaction
          event <- ctxFromProto(eventProto)
          reaction <- reactionProto.asMessage.sealedValue match {
            case protobuf.FireSensoryEventReactionMessage.SealedValue.Received(_) =>
              Success(NotifyWhenReceived)
            case protobuf.FireSensoryEventReactionMessage.SealedValue.Completed(protobuf.NotifyWhenCompleted(waitForRetries)) =>
              versioned(waitForRetries, "waitForRetries").map(NotifyWhenCompleted.apply)
            case protobuf.FireSensoryEventReactionMessage.SealedValue.Both(protobuf.NotifyBoth(waitForRetriesProto, receiverProto)) =>
              for {
                waitForRetries <- versioned(waitForRetriesProto, "waitForRetries")
                receiverProto <- versioned(receiverProto, "receiver")
                receiver <- ctxFromProto(receiverProto)
              } yield NotifyBoth(waitForRetries, receiver)
            case protobuf.FireSensoryEventReactionMessage.SealedValue.OnEvent(protobuf.NotifyOnEvent(waitForRetriesProto, onEventProto)) =>
              for {
                waitForRetries <- versioned(waitForRetriesProto, "waitForRetries")
                onEvent <- versioned(onEventProto, "onEvent")
              } yield NotifyOnEvent(waitForRetries, onEvent)
            case protobuf.FireSensoryEventReactionMessage.SealedValue.Empty =>
              Failure(new IllegalStateException("Received Empty of the oneof FireSensoryEventReaction protocol message."))
          }
          time = FiniteDuration(timeout, TimeUnit.MILLISECONDS)
        } yield ProcessEvent(recipeInstanceId, event, message.correlationId, time, reaction)
    }

  implicit def processEventReceivedResponseProto: ProtoMap[ProcessEventReceivedResponse, protobuf.ProcessEventReceivedResponse] =
    new ProtoMap[ProcessEventReceivedResponse, protobuf.ProcessEventReceivedResponse] {

      val companion = protobuf.ProcessEventReceivedResponse

      def toProto(a: ProcessEventReceivedResponse): protobuf.ProcessEventReceivedResponse =
        protobuf.ProcessEventReceivedResponse(
          Some(SensoryEventStatusMappingHelper.toProto(a.status))
        )

      def fromProto(message: protobuf.ProcessEventReceivedResponse): Try[ProcessEventReceivedResponse] =
        versioned(message.status, "status").flatMap(
          SensoryEventStatusMappingHelper.fromProto
        ).map(ProcessEventReceivedResponse)
    }

  implicit def processEventCompletedResponseProto: ProtoMap[ProcessEventCompletedResponse, protobuf.ProcessEventCompletedResponse] =
    new ProtoMap[ProcessEventCompletedResponse, protobuf.ProcessEventCompletedResponse] {

      val companion = protobuf.ProcessEventCompletedResponse

      def toProto(a: ProcessEventCompletedResponse): protobuf.ProcessEventCompletedResponse =
        protobuf.ProcessEventCompletedResponse(
          Some(ctxToProto(a.result))
        )

      def fromProto(message: protobuf.ProcessEventCompletedResponse): Try[ProcessEventCompletedResponse] =
        versioned(message.result, "result").flatMap(
          ctxFromProto(_)
        ).map(ProcessEventCompletedResponse)
    }


  implicit def retryBlockedInteractionProto: ProtoMap[RetryBlockedInteraction, protobuf.RetryBlockedInteraction] =
    new ProtoMap[RetryBlockedInteraction, protobuf.RetryBlockedInteraction] {

      val companion = protobuf.RetryBlockedInteraction

      def toProto(a: RetryBlockedInteraction): protobuf.RetryBlockedInteraction =
        protobuf.RetryBlockedInteraction(Some(a.recipeInstanceId), Some(a.interactionName))

      def fromProto(message: protobuf.RetryBlockedInteraction): Try[RetryBlockedInteraction] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
          interactionName <- versioned(message.interactionName, "interactionName")
        } yield RetryBlockedInteraction(recipeInstanceId, interactionName)
    }

  implicit def resolveBlockedInteractionProto: ProtoMap[ResolveBlockedInteraction, protobuf.ResolveBlockedInteraction] =
    new ProtoMap[ResolveBlockedInteraction, protobuf.ResolveBlockedInteraction] {

      val companion = protobuf.ResolveBlockedInteraction

      def toProto(a: ResolveBlockedInteraction): protobuf.ResolveBlockedInteraction =
        protobuf.ResolveBlockedInteraction(Some(a.recipeInstanceId), Some(a.interactionName), Some(ctxToProto(a.output)))

      def fromProto(message: protobuf.ResolveBlockedInteraction): Try[ResolveBlockedInteraction] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
          interactionName <- versioned(message.interactionName, "interactionName")
          eventProto <- versioned(message.event, "event")
          event <- ctxFromProto(eventProto)
        } yield ResolveBlockedInteraction(recipeInstanceId, interactionName, event)
    }

  implicit def stopRetryingInteractionProto: ProtoMap[StopRetryingInteraction, protobuf.StopRetryingInteraction] =
    new ProtoMap[StopRetryingInteraction, protobuf.StopRetryingInteraction] {

      val companion = protobuf.StopRetryingInteraction

      def toProto(a: StopRetryingInteraction): protobuf.StopRetryingInteraction =
        protobuf.StopRetryingInteraction(Some(a.recipeInstanceId), Some(a.interactionName))

      def fromProto(message: protobuf.StopRetryingInteraction): Try[StopRetryingInteraction] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
          interactionName <- versioned(message.interactionName, "interactionName")
        } yield StopRetryingInteraction(recipeInstanceId, interactionName)
    }

  implicit def processEventResponseProto(implicit provider: AkkaSerializerProvider): ProtoMap[ProcessEventResponse, protobuf.ProcessEventResponse] =
    new ProtoMap[ProcessEventResponse, protobuf.ProcessEventResponse] {

      val companion = protobuf.ProcessEventResponse

      def toProto(a: ProcessEventResponse): protobuf.ProcessEventResponse =
        protobuf.ProcessEventResponse(Some(a.recipeInstanceId), None)

      def fromProto(message: protobuf.ProcessEventResponse): Try[ProcessEventResponse] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        } yield ProcessEventResponse(recipeInstanceId)
    }

  implicit def addRecipeInstanceMetaDataProto(implicit provider: AkkaSerializerProvider): ProtoMap[AddRecipeInstanceMetaData, protobuf.AddRecipeInstanceMetaData] =
    new ProtoMap[AddRecipeInstanceMetaData, protobuf.AddRecipeInstanceMetaData] {

      val companion = protobuf.AddRecipeInstanceMetaData

      def toProto(a: AddRecipeInstanceMetaData): protobuf.AddRecipeInstanceMetaData =
        protobuf.AddRecipeInstanceMetaData(
          Some(a.recipeInstanceId),
          a.metaData.map(record => {
            protobuf.AddRecipeInstanceMetaDataRecord(Some(record._1), Some(record._2))}).toSeq)

      def fromProto(message: protobuf.AddRecipeInstanceMetaData): Try[AddRecipeInstanceMetaData] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
          metaData = message.metaData.map(record => (record.getKey -> record.getValue)).toMap
        } yield AddRecipeInstanceMetaData(recipeInstanceId, metaData)
    }

  implicit def getProcessStateProto: ProtoMap[GetProcessState, protobuf.GetProcessState] =
    new ProtoMap[GetProcessState, protobuf.GetProcessState] {

      val companion = protobuf.GetProcessState

      def toProto(a: GetProcessState): protobuf.GetProcessState =
        protobuf.GetProcessState(Some(a.recipeInstanceId))

      def fromProto(message: protobuf.GetProcessState): Try[GetProcessState] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        } yield GetProcessState(recipeInstanceId)
    }

  implicit def getCompiledRecipeProto: ProtoMap[GetCompiledRecipe, protobuf.GetCompiledRecipe] =
    new ProtoMap[GetCompiledRecipe, protobuf.GetCompiledRecipe] {

      val companion = protobuf.GetCompiledRecipe

      def toProto(a: GetCompiledRecipe): protobuf.GetCompiledRecipe =
        protobuf.GetCompiledRecipe(Some(a.recipeInstanceId))

      def fromProto(message: protobuf.GetCompiledRecipe): Try[GetCompiledRecipe] =
        for {
          recipeInstanceId <- versioned(message.recipeId, "recipeId")
        } yield GetCompiledRecipe(recipeInstanceId)
    }

  implicit def receivePeriodExpiredProtoSERejection: ProtoMap[FireSensoryEventRejection.ReceivePeriodExpired, protobuf.ReceivePeriodExpired] =
    new ProtoMap[FireSensoryEventRejection.ReceivePeriodExpired, protobuf.ReceivePeriodExpired] {

      val companion = protobuf.ReceivePeriodExpired

      def toProto(a: FireSensoryEventRejection.ReceivePeriodExpired): protobuf.ReceivePeriodExpired =
        protobuf.ReceivePeriodExpired(Some(a.recipeInstanceId))

      def fromProto(message: protobuf.ReceivePeriodExpired): Try[FireSensoryEventRejection.ReceivePeriodExpired] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        } yield FireSensoryEventRejection.ReceivePeriodExpired(recipeInstanceId)
    }

  implicit def invalidEventProtoSERejection: ProtoMap[FireSensoryEventRejection.InvalidEvent, protobuf.InvalidEvent] =
    new ProtoMap[FireSensoryEventRejection.InvalidEvent, protobuf.InvalidEvent] {

      val companion = protobuf.InvalidEvent

      def toProto(a: FireSensoryEventRejection.InvalidEvent): protobuf.InvalidEvent =
        protobuf.InvalidEvent(Some(a.recipeInstanceId), Some(a.msg))

      def fromProto(message: protobuf.InvalidEvent): Try[FireSensoryEventRejection.InvalidEvent] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
          msg <- versioned(message.reason, "reason")
        } yield FireSensoryEventRejection.InvalidEvent(recipeInstanceId, msg)
    }

  implicit def processDeletedProto: ProtoMap[ProcessDeleted, protobuf.ProcessDeleted] =
    new ProtoMap[ProcessDeleted, protobuf.ProcessDeleted] {

      val companion = protobuf.ProcessDeleted

      def toProto(a: ProcessDeleted): protobuf.ProcessDeleted =
        protobuf.ProcessDeleted(Some(a.recipeInstanceId))

      def fromProto(message: protobuf.ProcessDeleted): Try[ProcessDeleted] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
        } yield ProcessDeleted(recipeInstanceId)
    }

  implicit def processDeletedProtoSERejection: ProtoMap[FireSensoryEventRejection.RecipeInstanceDeleted, protobuf.ProcessDeleted] =
    new ProtoMap[FireSensoryEventRejection.RecipeInstanceDeleted, protobuf.ProcessDeleted] {

      val companion = protobuf.ProcessDeleted

      def toProto(a: FireSensoryEventRejection.RecipeInstanceDeleted): protobuf.ProcessDeleted =
        protobuf.ProcessDeleted(Some(a.recipeInstanceId))

      def fromProto(message: protobuf.ProcessDeleted): Try[FireSensoryEventRejection.RecipeInstanceDeleted] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        } yield FireSensoryEventRejection.RecipeInstanceDeleted(recipeInstanceId)
    }

  implicit def noSuchProcessProtoSERejection: ProtoMap[FireSensoryEventRejection.NoSuchRecipeInstance, protobuf.NoSuchProcess] =
    new ProtoMap[FireSensoryEventRejection.NoSuchRecipeInstance, protobuf.NoSuchProcess] {

      val companion = protobuf.NoSuchProcess

      def toProto(a: FireSensoryEventRejection.NoSuchRecipeInstance): protobuf.NoSuchProcess =
        protobuf.NoSuchProcess(Some(a.recipeInstanceId))

      def fromProto(message: protobuf.NoSuchProcess): Try[FireSensoryEventRejection.NoSuchRecipeInstance] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        } yield FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId)
    }

  implicit def firingLimitMetProtoSERejection: ProtoMap[FireSensoryEventRejection.FiringLimitMet, protobuf.FiringLimitMet] =
    new ProtoMap[FireSensoryEventRejection.FiringLimitMet, protobuf.FiringLimitMet] {

      val companion = protobuf.FiringLimitMet

      def toProto(a: FireSensoryEventRejection.FiringLimitMet): protobuf.FiringLimitMet =
        protobuf.FiringLimitMet(Some(a.recipeInstanceId))

      def fromProto(message: protobuf.FiringLimitMet): Try[FireSensoryEventRejection.FiringLimitMet] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        } yield FireSensoryEventRejection.FiringLimitMet(recipeInstanceId)
    }


  implicit def alreadyReceivedProtoSERejection: ProtoMap[FireSensoryEventRejection.AlreadyReceived, protobuf.SensoryEventAlreadyReceived] =
    new ProtoMap[FireSensoryEventRejection.AlreadyReceived, protobuf.SensoryEventAlreadyReceived] {

      val companion = protobuf.SensoryEventAlreadyReceived

      def toProto(a: FireSensoryEventRejection.AlreadyReceived): protobuf.SensoryEventAlreadyReceived =
        protobuf.SensoryEventAlreadyReceived(Some(a.recipeInstanceId), Some(a.correlationId))

      def fromProto(message: protobuf.SensoryEventAlreadyReceived): Try[FireSensoryEventRejection.AlreadyReceived] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
          correlationId <- versioned(message.correlationId, "correlationId")
        } yield FireSensoryEventRejection.AlreadyReceived(recipeInstanceId, correlationId)
    }


  implicit def noSuchProcessProto: ProtoMap[NoSuchProcess, protobuf.NoSuchProcess] =
    new ProtoMap[NoSuchProcess, protobuf.NoSuchProcess] {

      val companion = protobuf.NoSuchProcess

      def toProto(a: NoSuchProcess): protobuf.NoSuchProcess =
        protobuf.NoSuchProcess(Some(a.recipeInstanceId))

      def fromProto(message: protobuf.NoSuchProcess): Try[NoSuchProcess] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        } yield NoSuchProcess(recipeInstanceId)
    }

  implicit def processAlreadyExistsProto: ProtoMap[ProcessAlreadyExists, protobuf.ProcessAlreadyExists] =
    new ProtoMap[ProcessAlreadyExists, protobuf.ProcessAlreadyExists] {

      val companion = protobuf.ProcessAlreadyExists

      def toProto(a: ProcessAlreadyExists): protobuf.ProcessAlreadyExists =
        protobuf.ProcessAlreadyExists(Some(a.recipeInstanceId))

      def fromProto(message: protobuf.ProcessAlreadyExists): Try[ProcessAlreadyExists] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
        } yield ProcessAlreadyExists(recipeInstanceId)
    }

}
