package com.ing.baker.runtime.akka.actor.interaction_schedulling

import akka.actor.ActorRef

/**
  * Protocol done to find a possible matching between a QuestMandated and an available InteractionAgent
  */
sealed trait ProtocolPushPullMatching

object ProtocolPushPullMatching {

  def pushTopic(interactionName: String): String =
    s"Push|:||:|$interactionName|:|"

  def pullTopic(interactionName: String): String =
    s"Pull|:||:|$interactionName|:|"

  case class Push(mandated: ActorRef) extends ProtocolPushPullMatching

  case class Pull(agent: ActorRef) extends ProtocolPushPullMatching

  case class AvailableQuest(mandated: ActorRef) extends ProtocolPushPullMatching

}
