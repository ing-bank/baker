package com.ing.baker.runtime.actor.serialization.modules

import java.util.concurrent.TimeUnit

import akka.stream.SourceRef
import com.ing.baker.runtime.actor.ClusterBakerActorProvider.GetShardIndex
import com.ing.baker.runtime.actor.process_index.ProcessIndex.{Active, Deleted, ProcessStatus}
import com.ing.baker.runtime.actor.process_index.{ProcessIndex, ProcessIndexProtocol => protocol, protobuf}
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

    case protocol.GetIndex =>
      protobuf.GetIndex()

    case GetShardIndex(entityId) =>
    protobuf.GetShardIndex(Some(entityId))

    case protocol.Index(entries) =>
      protobuf.Index(entries.map(e => ctx.toProto[protobuf.ActorMetaData](e)).toList)

    case ProcessIndex.ActorMetadata(recipeId, processId, createdDateTime, processStatus) =>
      val isDeleted = processStatus == Deleted
      protobuf.ActorMetaData(Some(recipeId), Some(processId), Some(createdDateTime), Some(isDeleted))

    case protocol.CreateProcess(recipeId, processId) =>
      protobuf.CreateProcess(Some(recipeId), Some(processId))

    case protocol.ProcessEvent(processId, event, correlationId, waitForRetries, timeout) =>
      protobuf.ProcessEvent(Some(processId), Some(ctx.toProto[RuntimeEvent](event)), correlationId, Some(waitForRetries), Some(timeout.toMillis))

    case protocol.RetryBlockedInteraction(processId, interactionName) =>
      protobuf.RetryBlockedInteraction(Some(processId), Some(interactionName))

    case protocol.ResolveBlockedInteraction(processId, interactionName, event) =>
      protobuf.ResolveBlockedInteraction(Some(processId), Some(interactionName), Some(ctx.toProto[RuntimeEvent](event)))

    case protocol.StopRetryingInteraction(processId, interactionName) =>
      protobuf.StopRetryingInteraction(Some(processId), Some(interactionName))

    case protocol.ProcessEventResponse(processId, sourceRef) =>
      val serializedSourceRef = ctx.toProtoAny(sourceRef)
      protobuf.ProcessEventResponse(Some(processId), Some(serializedSourceRef))

    case protocol.GetProcessState(processId) =>
      protobuf.GetProcessState(Some(processId))

    case protocol.GetCompiledRecipe(recipeId) =>
      protobuf.GetCompiledRecipe(Some(recipeId))

    case protocol.ReceivePeriodExpired(processId) =>
      protobuf.ReceivePeriodExpired(Some(processId))

    case protocol.InvalidEvent(processId, reason) =>
      protobuf.InvalidEvent(Some(processId), Some(reason))

    case protocol.ProcessDeleted(processId) =>
      protobuf.ProcessDeleted(Some(processId))

    case protocol.NoSuchProcess(processId) =>
      protobuf.NoSuchProcess(Some(processId))

    case protocol.ProcessAlreadyExists(processId) =>
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
      protocol.GetIndex

    case protobuf.GetShardIndex(Some(entityId)) =>
      GetShardIndex(entityId)

    case protobuf.Index(entries) =>
      protocol.Index(entries.map(e => ctx.toDomain[ProcessIndex.ActorMetadata](e)))

    case protobuf.ActorMetaData(Some(recipeId), Some(processId), Some(createdTimeMillis), Some(isDeleted)) =>
      val processStatus: ProcessStatus = if (isDeleted) Deleted else Active
      ProcessIndex.ActorMetadata(recipeId, processId, createdTimeMillis, processStatus)

    case protobuf.CreateProcess(Some(recipeId), Some(processId)) =>
      protocol.CreateProcess(recipeId, processId)

    case protobuf.ProcessEvent(Some(processId), Some(event), correlationId, Some(waitForRetries), Some(timeoutMillis)) =>
      protocol.ProcessEvent(processId, ctx.toDomain[core.RuntimeEvent](event), correlationId, waitForRetries, FiniteDuration(timeoutMillis, TimeUnit.MILLISECONDS))

    case protobuf.RetryBlockedInteraction(Some(processId), Some(interactionName)) =>
      protocol.RetryBlockedInteraction(processId, interactionName)

    case protobuf.ResolveBlockedInteraction(Some(processId), Some(interactionName), Some(event)) =>
      protocol.ResolveBlockedInteraction(processId, interactionName, ctx.toDomain[core.RuntimeEvent](event))

    case protobuf.StopRetryingInteraction(Some(processId), Some(interactionName)) =>
      protocol.StopRetryingInteraction(processId, interactionName)

    case protobuf.ProcessEventResponse(Some(processId), Some(sourceRef)) =>
      val deserializedSourceRef = ctx.toDomain[SourceRef[Any]](sourceRef)
      protocol.ProcessEventResponse(processId, deserializedSourceRef)

    case protobuf.GetProcessState(Some(processId)) =>
      protocol.GetProcessState(processId)

    case protobuf.GetCompiledRecipe(Some(recipeId)) =>
      protocol.GetCompiledRecipe(recipeId)

    case protobuf.ReceivePeriodExpired(Some(processId)) =>
      protocol.ReceivePeriodExpired(processId)

    case protobuf.InvalidEvent(Some(processId), Some(reason)) =>
      protocol.InvalidEvent(processId, reason)

    case protobuf.ProcessDeleted(Some(processId)) =>
      protocol.ProcessDeleted(processId)

    case protobuf.NoSuchProcess(Some(processId)) =>
      protocol.NoSuchProcess(processId)

    case protobuf.ProcessAlreadyExists(Some(processId)) =>
      protocol.ProcessAlreadyExists(processId)
  }
}
