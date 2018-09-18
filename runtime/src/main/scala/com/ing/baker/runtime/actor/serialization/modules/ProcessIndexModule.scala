package com.ing.baker.runtime.actor.serialization.modules

import java.util.concurrent.TimeUnit

import com.ing.baker.runtime.actor.process_index.ProcessIndex.{Active, Deleted, ProcessStatus}
import com.ing.baker.runtime.actor.process_index.{ProcessIndex, ProcessIndexProtocol, protobuf}
import com.ing.baker.runtime.actor.protobuf.RuntimeEvent
import com.ing.baker.runtime.core

import scala.concurrent.duration.FiniteDuration

class ProcessIndexModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapterContext): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
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

    case ProcessIndexProtocol.Index(entries) =>
      protobuf.Index(entries.map(e => ctx.toProtoType[protobuf.ActorMetaData](e)).toList)

    case ProcessIndex.ActorMetadata(recipeId, processId, createdDateTime, processStatus) =>
      val isDeleted = processStatus == Deleted
      protobuf.ActorMetaData(Some(recipeId), Some(processId), Some(createdDateTime), Some(isDeleted))

    case ProcessIndexProtocol.CreateProcess(recipeId, processId) =>
      protobuf.CreateProcess(Some(recipeId), Some(processId))

    case ProcessIndexProtocol.ProcessEvent(processId, event, correlationId, waitForRetries, timeout) =>
      protobuf.ProcessEvent(Some(processId), Some(ctx.toProtoType[RuntimeEvent](event)), correlationId, Some(waitForRetries), Some(timeout.toMillis))
  }

  override def toDomain(ctx: ProtoEventAdapterContext): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {
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

    case protobuf.Index(entries) =>
      ProcessIndexProtocol.Index(entries.map(e => ctx.toDomainType[ProcessIndex.ActorMetadata](e)))

    case protobuf.ActorMetaData(Some(recipeId), Some(processId), Some(createdTimeMillis), Some(isDeleted)) =>
      val processStatus: ProcessStatus = if (isDeleted) Deleted else Active
      ProcessIndex.ActorMetadata(recipeId, processId, createdTimeMillis, processStatus)

    case protobuf.CreateProcess(Some(recipeId), Some(processId)) =>
      ProcessIndexProtocol.CreateProcess(recipeId, processId)

    case protobuf.ProcessEvent(Some(processId), Some(event), correlationId, Some(waitForRetries), Some(timeoutMillis)) =>
      ProcessIndexProtocol.ProcessEvent(processId, ctx.toDomainType[core.RuntimeEvent](event), correlationId, waitForRetries, FiniteDuration(timeoutMillis, TimeUnit.MILLISECONDS))
  }
}
