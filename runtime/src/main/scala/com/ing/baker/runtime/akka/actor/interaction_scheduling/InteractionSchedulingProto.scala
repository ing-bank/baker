package com.ing.baker.runtime.akka.actor.interaction_scheduling

import java.util.UUID

import cats.implicits._
import com.ing.baker.runtime.akka.actor.interaction_scheduling.ProtocolInteractionExecution.{ExecuteInstance, InstanceExecutedSuccessfully, InstanceExecutionFailed, InstanceExecutionTimedOut, InvalidExecution, NoInstanceFound}
import com.ing.baker.runtime.akka.actor.interaction_scheduling.ProtocolPushPullMatching.{AvailableQuest, Pull, Push}
import com.ing.baker.runtime.akka.actor.interaction_scheduling.ProtocolQuestCommit.{Commit, Considering, QuestTaken}
import com.ing.baker.runtime.akka.actor.serialization.{ProtoMap, SerializersProvider}
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}

import scala.util.{Success, Try}

object InteractionSchedulingProto {

  implicit def executeInstanceProto: ProtoMap[ExecuteInstance, protobuf.ExecuteInstance] =
    new ProtoMap[ExecuteInstance, protobuf.ExecuteInstance] {

      val companion = protobuf.ExecuteInstance

      def toProto(a: ExecuteInstance): protobuf.ExecuteInstance =
        protobuf.ExecuteInstance(a.input.map(ctxToProto(_)))

      def fromProto(message: protobuf.ExecuteInstance): Try[ExecuteInstance] =
        for {
          result <- message.input.toList.traverse(ctxFromProto(_))
        } yield ExecuteInstance(result)
    }

  implicit def instanceExcutedSuccessfullyProto: ProtoMap[InstanceExecutedSuccessfully, protobuf.InstanceExecutedSuccessfully] =
    new ProtoMap[InstanceExecutedSuccessfully, protobuf.InstanceExecutedSuccessfully] {

      val companion = protobuf.InstanceExecutedSuccessfully

      def toProto(a: InstanceExecutedSuccessfully): protobuf.InstanceExecutedSuccessfully =
        protobuf.InstanceExecutedSuccessfully(a.result.map(ctxToProto(_)))

      def fromProto(message: protobuf.InstanceExecutedSuccessfully): Try[InstanceExecutedSuccessfully] =
        for {
          result <- message.result.traverse(ctxFromProto(_))
        } yield InstanceExecutedSuccessfully(result)
    }

  implicit def instanceExecutionFailedProto: ProtoMap[InstanceExecutionFailed, protobuf.InstanceExecutionFailed] =
    new ProtoMap[InstanceExecutionFailed, protobuf.InstanceExecutionFailed] {

      val companion = protobuf.InstanceExecutionFailed

      def toProto(a: InstanceExecutionFailed): protobuf.InstanceExecutionFailed =
        protobuf.InstanceExecutionFailed()

      def fromProto(message: protobuf.InstanceExecutionFailed): Try[InstanceExecutionFailed] =
        Success(InstanceExecutionFailed())
    }

  implicit def instanceExecutionTimedOutProto: ProtoMap[InstanceExecutionTimedOut, protobuf.InstanceExecutionTimedOut] =
    new ProtoMap[InstanceExecutionTimedOut, protobuf.InstanceExecutionTimedOut] {

      val companion = protobuf.InstanceExecutionTimedOut

      def toProto(a: InstanceExecutionTimedOut): protobuf.InstanceExecutionTimedOut =
        protobuf.InstanceExecutionTimedOut()

      def fromProto(message: protobuf.InstanceExecutionTimedOut): Try[InstanceExecutionTimedOut] =
        Success(InstanceExecutionTimedOut())
    }

  implicit def noInstanceFoundProto: ProtoMap[NoInstanceFound.type, protobuf.NoInstanceFound] =
    new ProtoMap[NoInstanceFound.type, protobuf.NoInstanceFound] {

      val companion = protobuf.NoInstanceFound

      def toProto(a: NoInstanceFound.type): protobuf.NoInstanceFound =
        protobuf.NoInstanceFound()

      def fromProto(message: protobuf.NoInstanceFound): Try[NoInstanceFound.type] =
        Success(NoInstanceFound)
    }

  implicit def invalidExecutionProto: ProtoMap[InvalidExecution, protobuf.InvalidExecution] =
    new ProtoMap[InvalidExecution, protobuf.InvalidExecution] {

      val companion = protobuf.InvalidExecution

      def toProto(a: InvalidExecution): protobuf.InvalidExecution =
        protobuf.InvalidExecution()

      def fromProto(message: protobuf.InvalidExecution): Try[InvalidExecution] =
        Success(InvalidExecution())
    }

  implicit def pushProto(implicit ev0: SerializersProvider): ProtoMap[Push, protobuf.Push] =
    new ProtoMap[Push, protobuf.Push] {

      val companion = protobuf.Push

      def toProto(a: Push): protobuf.Push =
        protobuf.Push(Some(ctxToProto(a.mandated)), Some(a.uuid.toString))

      def fromProto(message: protobuf.Push): Try[Push] =
        for {
          mandatedId <- versioned(message.mandated, "mandated")
          mandated <- ctxFromProto(mandatedId)
          uuidRaw <- versioned(message.uuid, "uuid")
          uuid <- Try(UUID.fromString(uuidRaw))
        } yield Push(mandated, uuid)
    }

  implicit def pullProto(implicit ev0: SerializersProvider): ProtoMap[Pull, protobuf.Pull] =
    new ProtoMap[Pull, protobuf.Pull] {

      val companion = protobuf.Pull

      def toProto(a: Pull): protobuf.Pull =
        protobuf.Pull(Some(ctxToProto(a.agent)))

      def fromProto(message: protobuf.Pull): Try[Pull] =
        for {
          agentId <- versioned(message.agent, "agent")
          agent <- ctxFromProto(agentId)
        } yield Pull(agent)
    }

  implicit def availableQuestProto(implicit ev0: SerializersProvider): ProtoMap[AvailableQuest, protobuf.AvailableQuest] =
    new ProtoMap[AvailableQuest, protobuf.AvailableQuest] {

      val companion = protobuf.AvailableQuest

      def toProto(a: AvailableQuest): protobuf.AvailableQuest =
        protobuf.AvailableQuest(Some(ctxToProto(a.mandated)), Some(a.uuid.toString))

      def fromProto(message: protobuf.AvailableQuest): Try[AvailableQuest] =
        for {
          mandatedId <- versioned(message.mandated, "mandated")
          mandated <- ctxFromProto(mandatedId)
          uuidRaw <- versioned(message.uuid, "uuid")
          uuid <- Try(UUID.fromString(uuidRaw))
        } yield AvailableQuest(mandated, uuid)
    }

  implicit def consideringProto(implicit ev0: SerializersProvider): ProtoMap[Considering, protobuf.Considering] =
    new ProtoMap[Considering, protobuf.Considering] {

      val companion = protobuf.Considering

      def toProto(a: Considering): protobuf.Considering =
        protobuf.Considering(Some(ctxToProto(a.agent)))

      def fromProto(message: protobuf.Considering): Try[Considering] =
        for {
          agentId <- versioned(message.agent, "agent")
          agent <- ctxFromProto(agentId)
        } yield Considering(agent)
    }

  implicit def commitProto(implicit ev0: SerializersProvider): ProtoMap[Commit, protobuf.Commit] =
    new ProtoMap[Commit, protobuf.Commit] {

      val companion = protobuf.Commit

      def toProto(a: Commit): protobuf.Commit =
        protobuf.Commit(Some(ctxToProto(a.mandated)), Some(ctxToProto(a.execute)))

      def fromProto(message: protobuf.Commit): Try[Commit] =
        for {
          mandatedId <- versioned(message.mandated, "mandated")
          mandated <- ctxFromProto(mandatedId)
          executeProto <- versioned(message.execute, "execute")
          execute <- ctxFromProto(executeProto)
        } yield Commit(mandated, execute)
    }

  implicit def questTakenProto: ProtoMap[QuestTaken.type, protobuf.QuestTaken] =
    new ProtoMap[QuestTaken.type, protobuf.QuestTaken] {

      val companion = protobuf.QuestTaken

      def toProto(a: QuestTaken.type): protobuf.QuestTaken =
        protobuf.QuestTaken()

      def fromProto(message: protobuf.QuestTaken): Try[QuestTaken.type] =
        Success(QuestTaken)
    }
}
