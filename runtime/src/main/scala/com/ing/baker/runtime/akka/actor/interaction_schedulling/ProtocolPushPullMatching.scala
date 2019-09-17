package com.ing.baker.runtime.akka.actor.interaction_schedulling

import akka.actor.ActorRef

/**
  * Protocol done to find a possible matching between a QuestMandated and an available InteractionAgent
  */
sealed trait ProtocolPushPullMatching

object ProtocolPushPullMatching {

  def pushTopic(recipeName: String, interactionName: String, version: String): String =
    s"Push|:|$recipeName|:|$interactionName|:|$version"

  def pullTopic(recipeName: String, interactionName: String, version: String): String =
    s"Pull|:|$recipeName|:|$interactionName|:|$version"

  case class Push(mandated: ActorRef) extends ProtocolPushPullMatching

  case class Pull(agent: ActorRef) extends ProtocolPushPullMatching

  case class AvailableQuest(mandated: ActorRef) extends ProtocolPushPullMatching

}
