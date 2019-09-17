package com.ing.baker.runtime.akka.actor.interaction_schedulling

import akka.actor.ActorRef

/**
  * A Protocol executed after finding a candidate match between a QuestMandated and an InteractionAgent, it makes sure
  * that 1 QuestMandated commits with 1 InteractionAgent only and vice versa, without leaving orphan agents.
  */
sealed trait ProtocolQuestCommit

object ProtocolQuestCommit {

  case class Considering(agent: ActorRef) extends ProtocolQuestCommit

  case class Commit(mandated: ActorRef, execute: ProtocolInteractionExecution.ExecuteInstance) extends ProtocolQuestCommit

  case object QuestTaken extends ProtocolQuestCommit
}
