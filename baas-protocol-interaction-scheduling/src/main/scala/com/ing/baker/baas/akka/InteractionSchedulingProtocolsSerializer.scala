package com.ing.baker.baas.akka

import akka.actor.ExtendedActorSystem
import com.ing.baker.runtime.serialization.{SerializersProvider, TypedProtobufSerializer}
import com.ing.baker.runtime.serialization.TypedProtobufSerializer.{BinarySerializable, forType}
import com.ing.baker.baas.protocol.InteractionSchedulingProto._

object InteractionSchedulingProtocolsSerializer {

  val identifier: Int = 102

  def entries(ev0: SerializersProvider): List[BinarySerializable] = {
    implicit val ev = ev0
    List(
      forType[com.ing.baker.baas.protocol.ProtocolInteractionExecution.ExecuteInstance]
        .register("com.ing.baker.baas.protocol.ProtocolInteractionExecution.ExecuteInstance"),
      forType[com.ing.baker.baas.protocol.ProtocolInteractionExecution.InstanceExecutedSuccessfully]
        .register("com.ing.baker.baas.protocol.ProtocolInteractionExecution.InstanceExecutedSuccessfully"),
      forType[com.ing.baker.baas.protocol.ProtocolInteractionExecution.InstanceExecutionFailed]
        .register("com.ing.baker.baas.protocol.ProtocolInteractionExecution.InstanceExecutionFailed"),
      forType[com.ing.baker.baas.protocol.ProtocolInteractionExecution.InstanceExecutionTimedOut]
        .register("com.ing.baker.baas.protocol.ProtocolInteractionExecution.InstanceExecutionTimedOut"),
      forType[com.ing.baker.baas.protocol.ProtocolInteractionExecution.NoInstanceFound.type]
        .register("com.ing.baker.baas.protocol.ProtocolInteractionExecution.NoInstanceFound"),
      forType[com.ing.baker.baas.protocol.ProtocolInteractionExecution.InvalidExecution]
        .register("com.ing.baker.baas.protocol.ProtocolInteractionExecution.InvalidExecution"),
      forType[com.ing.baker.baas.protocol.ProtocolPushPullMatching.Push]
        .register("com.ing.baker.baas.protocol.ProtocolPushPullMatching.Push"),
      forType[com.ing.baker.baas.protocol.ProtocolPushPullMatching.Pull]
        .register("com.ing.baker.baas.protocol.ProtocolPushPullMatching.Pull"),
      forType[com.ing.baker.baas.protocol.ProtocolPushPullMatching.AvailableQuest]
        .register("com.ing.baker.baas.protocol.ProtocolPushPullMatching.AvailableQuest"),
      forType[com.ing.baker.baas.protocol.ProtocolQuestCommit.Considering]
        .register("com.ing.baker.baas.protocol.ProtocolQuestCommit.Considering"),
      forType[com.ing.baker.baas.protocol.ProtocolQuestCommit.Commit]
        .register("com.ing.baker.baas.protocol.ProtocolQuestCommit.Commit"),
      forType[com.ing.baker.baas.protocol.ProtocolQuestCommit.QuestTaken.type]
        .register("com.ing.baker.baas.protocol.ProtocolQuestCommit.QuestTaken")
    )
  }
}

class InteractionSchedulingProtocolsSerializer(system: ExtendedActorSystem) extends TypedProtobufSerializer(system, InteractionSchedulingProtocolsSerializer.identifier ,InteractionSchedulingProtocolsSerializer.entries)
