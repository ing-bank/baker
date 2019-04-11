package com.ing.baker.runtime.actor.process_index

import java.util.concurrent.TimeUnit

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.runtime.actor.ClusterBakerActorProvider.GetShardIndex
import com.ing.baker.runtime.actor.process_index.ProcessIndex._
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.actortyped.serialization.BinarySerializable
import com.ing.baker.runtime.actortyped.serialization.ProtoMap.{versioned, ctxFromProto, ctxToProto}

import scala.concurrent.duration.FiniteDuration
import scala.util.Try

object ProcessIndexSerialization {

  def getShardIndex: BinarySerializable =
    new BinarySerializable {

      type Type = GetShardIndex

      val tag: Class[GetShardIndex] = classOf[GetShardIndex]

      def manifest: String = "ProcessIndex.GetShardIndex"

      def toBinary(a: GetShardIndex): Array[Byte] =
        protobuf.GetShardIndex(Some(a.entityId)).toByteArray

      def fromBinary(binary: Array[Byte]): Try[GetShardIndex] =
        for {
          message <- Try(protobuf.GetShardIndex.parseFrom(binary))
          entityId <- versioned(message.entityId, "entityId")
        } yield GetShardIndex(entityId)
    }

  def actorCreated: BinarySerializable =
    new BinarySerializable {

      type Type = ActorCreated

      val tag: Class[ActorCreated] = classOf[ActorCreated]

      def manifest: String = "ProcessIndex.ActorCreated"

      def toBinary(a: ActorCreated): Array[Byte] =
        protobuf.ActorCreated(Some(a.recipeId), Some(a.processId), Some(a.createdDateTime)).toByteArray

      def fromBinary(binary: Array[Byte]): Try[ActorCreated] =
        for {
          message <- Try(protobuf.ActorCreated.parseFrom(binary))
          recipeId <- versioned(message.recipeId, "recipeId")
          processId <- versioned(message.processId, "processId")
          createdDateTime <- versioned(message.dateCreated, "dateCreated")
        } yield ActorCreated(recipeId, processId, createdDateTime)
    }

  def actorDeleted: BinarySerializable =
    new BinarySerializable {

      type Type = ActorDeleted

      val tag: Class[ActorDeleted] = classOf[ActorDeleted]

      def manifest: String = "ProcessIndex.ActorDeleted"

      def toBinary(a: ActorDeleted): Array[Byte] =
        protobuf.ActorDeleted(Some(a.processId)).toByteArray

      def fromBinary(binary: Array[Byte]): Try[ActorDeleted] =
        for {
          message <- Try(protobuf.ActorDeleted.parseFrom(binary))
          processId <- versioned(message.processId, "processId")
        } yield ActorDeleted(processId)
    }

  def actorPassivated: BinarySerializable =
    new BinarySerializable {

      type Type = ActorPassivated

      val tag: Class[ActorPassivated] = classOf[ActorPassivated]

      def manifest: String = "ProcessIndex.ActorPassivated"

      def toBinary(a: ActorPassivated): Array[Byte] =
        protobuf.ActorPassivated(Some(a.processId)).toByteArray

      def fromBinary(binary: Array[Byte]): Try[ActorPassivated] =
        for {
          message <- Try(protobuf.ActorPassivated.parseFrom(binary))
          processId <- versioned(message.processId, "processId")
        } yield ActorPassivated(processId)
    }

  def actorActivated: BinarySerializable =
    new BinarySerializable {

      type Type = ActorActivated

      val tag: Class[ActorActivated] = classOf[ActorActivated]

      def manifest: String = "ProcessIndex.ActorActivated"

      def toBinary(a: ActorActivated): Array[Byte] =
        protobuf.ActorActivated(Some(a.processId)).toByteArray

      def fromBinary(binary: Array[Byte]): Try[ActorActivated] =
        for {
          message <- Try(protobuf.ActorActivated.parseFrom(binary))
          processId <- versioned(message.processId, "processId")
        } yield ActorActivated(processId)
    }

  def actorMetadata: BinarySerializable =
    new BinarySerializable {

      type Type = ActorMetadata

      val tag: Class[ActorMetadata] = classOf[ActorMetadata]

      def manifest: String = "ProcessIndex.ActorMetadata"

      def toBinary(a: ActorMetadata): Array[Byte] =
        protobuf.ActorMetaData(
          Some(a.recipeId),
          Some(a.processId),
          Some(a.createdDateTime),
          Some(a.processStatus == ProcessIndex.Deleted)
        ).toByteArray

      def fromBinary(binary: Array[Byte]): Try[ActorMetadata] =
        for {
          message <- Try(protobuf.ActorMetaData.parseFrom(binary))
          recipeId <- versioned(message.recipeId, "recipeId")
          processId <- versioned(message.processId, "processId")
          createdDateTime <- versioned(message.createdTime, "createdTime")
          isDeleted <- versioned(message.isDeleted, "createdTime")
          processStatus = if (isDeleted) ProcessIndex.Deleted else ProcessIndex.Active
        } yield ActorMetadata(recipeId, processId, createdDateTime, processStatus)
    }

  def getIndex: BinarySerializable =
    new BinarySerializable {

      type Type = GetIndex.type

      val tag: Class[_ <: Type] = GetIndex.getClass

      def manifest: String = "ProcessIndex.GetIndex"

      def toBinary(a: GetIndex.type): Array[Byte] =
        protobuf.GetIndex().toByteArray

      def fromBinary(binary: Array[Byte]): Try[GetIndex.type] =
        for {
          _ <- Try(protobuf.GetIndex.parseFrom(binary))
        } yield GetIndex
    }

  def index: BinarySerializable =
    new BinarySerializable {

      type Type = Index

      val tag: Class[Index] = classOf[Index]

      def manifest: String = "ProcessIndex.Index"

      def toBinary(a: Index): Array[Byte] =
        protobuf.Index(a.entries.map { e =>
          protobuf.ActorMetaData(
            Some(e.recipeId),
            Some(e.processId),
            Some(e.createdDateTime),
            Some(e.processStatus == ProcessIndex.Deleted)
          )
        }).toByteArray

      def fromBinary(binary: Array[Byte]): Try[Index] =
        for {
          message <- Try(protobuf.Index.parseFrom(binary))
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

  def createProcess: BinarySerializable =
    new BinarySerializable {

      type Type = CreateProcess

      val tag: Class[CreateProcess] = classOf[CreateProcess]

      def manifest: String = "ProcessIndex.CreateProcess"

      def toBinary(a: CreateProcess): Array[Byte] =
        protobuf.CreateProcess(Some(a.recipeId), Some(a.processId)).toByteArray

      def fromBinary(binary: Array[Byte]): Try[CreateProcess] =
        for {
          message <- Try(protobuf.CreateProcess.parseFrom(binary))
          recipeId <- versioned(message.recipeId, "recipeId")
          processId <- versioned(message.processId, "processId")
        } yield CreateProcess(recipeId, processId)
    }

  def processEvent: BinarySerializable =
    new BinarySerializable {

      type Type = ProcessEvent

      val tag: Class[ProcessEvent] = classOf[ProcessEvent]

      def manifest: String = "ProcessIndex.ProcessEvent"

      def toBinary(a: ProcessEvent): Array[Byte] =
        protobuf.ProcessEvent(
          Some(a.processId),
          Some(ctxToProto(a.event)),
          a.correlationId,
          Some(a.waitForRetries),
          Some(a.timeout.toMillis)
        ).toByteArray

      def fromBinary(binary: Array[Byte]): Try[ProcessEvent] =
        for {
          message <- Try(protobuf.ProcessEvent.parseFrom(binary))
          processId <- versioned(message.processId, "processId")
          eventProto <- versioned(message.event, "event")
          waitFor <- versioned(message.waitForRetries, "waitForRetries")
          timeout <- versioned(message.timeout, "timeout")
          event <- ctxFromProto(eventProto)
          time = FiniteDuration(timeout, TimeUnit.MILLISECONDS)
        } yield ProcessEvent(processId, event, message.correlationId, waitFor, time)
    }

  def retryBlockedInteraction: BinarySerializable =
    new BinarySerializable {

      type Type = RetryBlockedInteraction

      val tag: Class[RetryBlockedInteraction] = classOf[RetryBlockedInteraction]

      def manifest: String = "ProcessIndex.RetryBlockedInteraction"

      def toBinary(a: RetryBlockedInteraction): Array[Byte] =
        protobuf.RetryBlockedInteraction(Some(a.processId), Some(a.interactionName)).toByteArray

      def fromBinary(binary: Array[Byte]): Try[RetryBlockedInteraction] =
        for {
          message <- Try(protobuf.RetryBlockedInteraction.parseFrom(binary))
          processId <- versioned(message.processId, "processId")
          interactionName <- versioned(message.interactionName, "interactionName")
        } yield RetryBlockedInteraction(processId, interactionName)
    }

  def resolveBlockedInteraction: BinarySerializable =
    new BinarySerializable {

      type Type = ResolveBlockedInteraction

      val tag: Class[ResolveBlockedInteraction] = classOf[ResolveBlockedInteraction]

      def manifest: String = "ProcessIndex.ResolveBlockedInteraction"

      def toBinary(a: ResolveBlockedInteraction): Array[Byte] =
        protobuf.ResolveBlockedInteraction(Some(a.processId), Some(a.interactionName), Some(ctxToProto(a.output))).toByteArray

      def fromBinary(binary: Array[Byte]): Try[ResolveBlockedInteraction] =
        for {
          message <- Try(protobuf.ResolveBlockedInteraction.parseFrom(binary))
          processId <- versioned(message.processId, "processId")
          interactionName <- versioned(message.interactionName, "interactionName")
          eventProto <- versioned(message.event, "event")
          event <- ctxFromProto(eventProto)
        } yield ResolveBlockedInteraction(processId, interactionName, event)
    }

  def stopRetryingInteraction: BinarySerializable =
    new BinarySerializable {

      type Type = StopRetryingInteraction

      val tag: Class[StopRetryingInteraction] = classOf[StopRetryingInteraction]

      def manifest: String = "ProcessIndex.StopRetryingInteraction"

      def toBinary(a: StopRetryingInteraction): Array[Byte] =
        protobuf.StopRetryingInteraction(Some(a.processId), Some(a.interactionName)).toByteArray

      def fromBinary(binary: Array[Byte]): Try[StopRetryingInteraction] =
        for {
          message <- Try(protobuf.StopRetryingInteraction.parseFrom(binary))
          processId <- versioned(message.processId, "processId")
          interactionName <- versioned(message.interactionName, "interactionName")
        } yield StopRetryingInteraction(processId, interactionName)
    }

}
