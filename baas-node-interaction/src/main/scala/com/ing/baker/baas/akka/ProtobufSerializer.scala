package com.ing.baker.baas.akka

import akka.actor.ExtendedActorSystem
import com.ing.baker.baas.protocol.{ProtocolInteractionExecution, ProtocolPushPullMatching, ProtocolQuestCommit}
import com.ing.baker.baas.protocol.InteractionSchedulingProto._
import com.ing.baker.il
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceState}
import com.ing.baker.runtime.serialization.{SerializersProvider, TypedProtobufSerializer}
import com.ing.baker.runtime.serialization.TypedProtobufSerializer.{BinarySerializable, forType}

object ProtobufSerializer {

  def entries(ev0: SerializersProvider): List[BinarySerializable] = {
    implicit val ev = ev0
    commonEntries ++ interactionSchedulingEntries
  }

  def commonEntries(implicit ev0: SerializersProvider): List[BinarySerializable] =
    List(
      forType[com.ing.baker.types.Value]
        .register("baker.types.Value"),
      forType[com.ing.baker.types.Type]
        .register("baker.types.Type"),
      forType[EventInstance]
        .register("core.RuntimeEvent"),
      forType[RecipeInstanceState]
        .register("core.ProcessState"),
      forType[il.CompiledRecipe]
        .register("il.CompiledRecipe")
    )

  def interactionSchedulingEntries(implicit ev0: SerializersProvider): List[BinarySerializable] =
    List(
      forType[ProtocolInteractionExecution.InstanceExecutedSuccessfully]
        .register("InteractionSchedulingProtocols.InstanceExecutedSuccessfully"),
      forType[ProtocolInteractionExecution.InstanceExecutionFailed]
        .register("InteractionSchedulingProtocols.InstanceExecutionFailed"),
      forType[ProtocolInteractionExecution.InstanceExecutionTimedOut]
        .register("InteractionSchedulingProtocols.InstanceExecutionTimedOut"),
      forType[ProtocolInteractionExecution.NoInstanceFound.type]
        .register("InteractionSchedulingProtocols.NoInstanceFound"),
      forType[ProtocolInteractionExecution.InvalidExecution]
        .register("InteractionSchedulingProtocols.InvalidExecution"),
      forType[ProtocolPushPullMatching.Push]
        .register("InteractionSchedulingProtocols.Push"),
      forType[ProtocolPushPullMatching.Pull]
        .register("InteractionSchedulingProtocols.Pull"),
      forType[ProtocolPushPullMatching.AvailableQuest]
        .register("InteractionSchedulingProtocols.AvailableQuest"),
      forType[ProtocolQuestCommit.Considering]
        .register("InteractionSchedulingProtocols.Considering"),
      forType[ProtocolQuestCommit.Commit]
        .register("InteractionSchedulingProtocols.Commit"),
      forType[ProtocolQuestCommit.QuestTaken.type]
        .register("InteractionSchedulingProtocols.QuestTaken")
    )
}

class ProtobufSerializer(system: ExtendedActorSystem) extends TypedProtobufSerializer(system, ProtobufSerializer.entries)
