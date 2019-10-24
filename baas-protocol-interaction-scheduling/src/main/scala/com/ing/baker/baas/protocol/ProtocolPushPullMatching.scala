package com.ing.baker.baas.protocol

import java.util.UUID

import akka.actor.ActorRef

/**
  * Protocol done to find a possible matching between a QuestMandated and an available InteractionAgent
  */
sealed trait ProtocolPushPullMatching //extends BakerSerializable

object ProtocolPushPullMatching {

  def pushTopic(interactionName: String): String =
    s"Push|:||:|$interactionName|:|"

  def pullTopic(interactionName: String): String =
    s"Pull|:||:|$interactionName|:|"

  case class Push(mandated: ActorRef, uuid: UUID) extends ProtocolPushPullMatching

  case class Pull(agent: ActorRef) extends ProtocolPushPullMatching

  case class AvailableQuest(mandated: ActorRef, uuid: UUID) extends ProtocolPushPullMatching

}
