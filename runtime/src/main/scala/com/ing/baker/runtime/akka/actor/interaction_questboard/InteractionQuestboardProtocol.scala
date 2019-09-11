package com.ing.baker.runtime.akka.actor.interaction_questboard

import akka.actor.ActorRef

object InteractionQuestboardProtocol {

  case class GetQuest(namespace: String)

  case class GetQuestResponse(guild: ActorRef)

  case class PostQuest(namespace: String, guild: ActorRef)

  case class RemoveQuest(namespace: String, guild: ActorRef)
}
