package com.ing.baker.runtime.actor.serialization.modules

import java.util.concurrent.TimeUnit

import akka.stream.SourceRef
import com.ing.baker.runtime.actor.ClusterBakerActorProvider.GetShardIndex
import com.ing.baker.runtime.actor.process_index.ProcessIndex.{Active, Deleted, ProcessStatus}
import com.ing.baker.runtime.actor.process_index.{ProcessIndex, ProcessIndexProtocol, protobuf}
import com.ing.baker.runtime.actor.protobuf.RuntimeEvent
import com.ing.baker.runtime.actor.serialization.{ProtoEventAdapter, ProtoEventAdapterModule}
import com.ing.baker.runtime.core

import scala.concurrent.duration.FiniteDuration

class ProcessIndexModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case ProcessIndex.ActorCreated(recipeId, processId, createdDateTime) =>
      protobuf.ActorCreated(Option(recipeId), Option(processId), Option(createdDateTime))

    case ProcessIndex.ActorPassivated(processId) =>
      protobuf.ActorPassivated(Option(processId))

    case ProcessIndex.ActorActivated(processId) =>
      protobuf.ActorActivated(Option(processId))

    case ProcessIndex.ActorDeleted(processId) =>
      protobuf.ActorDeleted(Option(processId))

    case ProcessIndexProtocol.GetIndex =>
      protobuf.GetIndex()

    case GetShardIndex(entityId) =>
    protobuf.GetShardIndex(Some(entityId))

    case ProcessIndexProtocol.Index(entries) =>
      protobuf.Index(entries.map(e => ctx.toProto[protobuf.ActorMetaData](e)).toList)

    case ProcessIndex.ActorMetadata(recipeId, processId, createdDateTime, processStatus) =>
      val isDeleted = processStatus == Deleted
      protobuf.ActorMetaData(Some(recipeId), Some(processId), Some(createdDateTime), Some(isDeleted))

    case ProcessIndexProtocol.CreateProcess(recipeId, processId) =>
      protobuf.CreateProcess(Some(recipeId), Some(processId))

    case ProcessIndexProtocol.ProcessEvent(processId, event, correlationId, waitForRetries, timeout) =>
      protobuf.ProcessEvent(Some(processId), Some(ctx.toProto[RuntimeEvent](event)), correlationId, Some(waitForRetries), Some(timeout.toMillis))

    case ProcessIndexProtocol.ProcessEventResponse(processId, sourceRef) =>
      val serializedSourceRef = ctx.toProtoAny(sourceRef)
      protobuf.ProcessEventResponse(Some(processId), Some(serializedSourceRef))

    case ProcessIndexProtocol.GetProcessState(processId) =>
      protobuf.GetProcessState(Some(processId))

    case ProcessIndexProtocol.GetCompiledRecipe(recipeId) =>
      protobuf.GetCompiledRecipe(Some(recipeId))

    case ProcessIndexProtocol.ReceivePeriodExpired(processId) =>
      protobuf.ReceivePeriodExpired(Some(processId))

    case ProcessIndexProtocol.InvalidEvent(processId, reason) =>
      protobuf.InvalidEvent(Some(processId), Some(reason))

    case ProcessIndexProtocol.ProcessDeleted(processId) =>
      protobuf.ProcessDeleted(Some(processId))

    case ProcessIndexProtocol.NoSuchProcess(processId) =>
      protobuf.NoSuchProcess(Some(processId))

    case ProcessIndexProtocol.ProcessAlreadyExists(processId) =>
      protobuf.ProcessAlreadyExists(Some(processId))
  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {
    case protobuf.ActorCreated(Some(recipeId), Some(processId), Some(dateCreated)) =>
      ProcessIndex.ActorCreated(recipeId, processId, dateCreated)

    case protobuf.ActorPassivated(Some(processId)) =>
      ProcessIndex.ActorPassivated(processId)

    case protobuf.ActorActivated(Some(processId)) =>
      ProcessIndex.ActorActivated(processId)

    case protobuf.ActorDeleted(Some(processId)) =>
      ProcessIndex.ActorDeleted(processId)

    case protobuf.GetIndex() =>
      ProcessIndexProtocol.GetIndex

    case protobuf.GetShardIndex(Some(entityId)) =>
      GetShardIndex(entityId)

    case protobuf.Index(entries) =>
      ProcessIndexProtocol.Index(entries.map(e => ctx.toDomain[ProcessIndex.ActorMetadata](e)))

    case protobuf.ActorMetaData(Some(recipeId), Some(processId), Some(createdTimeMillis), Some(isDeleted)) =>
      val processStatus: ProcessStatus = if (isDeleted) Deleted else Active
      ProcessIndex.ActorMetadata(recipeId, processId, createdTimeMillis, processStatus)

    case protobuf.CreateProcess(Some(recipeId), Some(processId)) =>
      ProcessIndexProtocol.CreateProcess(recipeId, processId)

    case protobuf.ProcessEvent(Some(processId), Some(event), correlationId, Some(waitForRetries), Some(timeoutMillis)) =>
      ProcessIndexProtocol.ProcessEvent(processId, ctx.toDomain[core.RuntimeEvent](event), correlationId, waitForRetries, FiniteDuration(timeoutMillis, TimeUnit.MILLISECONDS))

    case protobuf.ProcessEventResponse(Some(processId), Some(sourceRef)) =>
      val deserializedSourceRef = ctx.toDomain[SourceRef[Any]](sourceRef)
      ProcessIndexProtocol.ProcessEventResponse(processId, deserializedSourceRef)

    case protobuf.GetProcessState(Some(processId)) =>
      ProcessIndexProtocol.GetProcessState(processId)

    case protobuf.GetCompiledRecipe(Some(recipeId)) =>
      ProcessIndexProtocol.GetCompiledRecipe(recipeId)

    case protobuf.ReceivePeriodExpired(Some(processId)) =>
      ProcessIndexProtocol.ReceivePeriodExpired(processId)

    case protobuf.InvalidEvent(Some(processId), Some(reason)) =>
      ProcessIndexProtocol.InvalidEvent(processId, reason)

    case protobuf.ProcessDeleted(Some(processId)) =>
      ProcessIndexProtocol.ProcessDeleted(processId)

    case protobuf.NoSuchProcess(Some(processId)) =>
      ProcessIndexProtocol.NoSuchProcess(processId)

    case protobuf.ProcessAlreadyExists(Some(processId)) =>
      ProcessIndexProtocol.ProcessAlreadyExists(processId)
  }
}
