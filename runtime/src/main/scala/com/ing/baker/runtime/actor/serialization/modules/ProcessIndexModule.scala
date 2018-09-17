package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.runtime.actor.process_index
import com.ing.baker.runtime.actor.process_index.ProcessIndex

class ProcessIndexModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapterContext): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case ProcessIndex.ActorCreated(recipeId, processId, createdDateTime) =>
      process_index.protobuf.ActorCreated(Option(recipeId), Option(processId), Option(createdDateTime))

    case ProcessIndex.ActorPassivated(processId) =>
      process_index.protobuf.ActorPassivated(Option(processId))

    case ProcessIndex.ActorActivated(processId) =>
      process_index.protobuf.ActorActivated(Option(processId))

    case ProcessIndex.ActorDeleted(processId) =>
      process_index.protobuf.ActorDeleted(Option(processId))

  }

  override def toDomain(ctx: ProtoEventAdapterContext): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {
    case process_index.protobuf.ActorCreated(Some(recipeId), Some(processId), Some(dateCreated)) =>
      ProcessIndex.ActorCreated(recipeId, processId, dateCreated)

    case process_index.protobuf.ActorPassivated(Some(processId)) =>
      ProcessIndex.ActorPassivated(processId)

    case process_index.protobuf.ActorActivated(Some(processId)) =>
      ProcessIndex.ActorActivated(processId)

    case process_index.protobuf.ActorDeleted(Some(processId)) =>
      ProcessIndex.ActorDeleted(processId)

  }

}
