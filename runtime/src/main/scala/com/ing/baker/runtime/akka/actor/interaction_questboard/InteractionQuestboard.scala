package com.ing.baker.runtime.akka.actor.interaction_questboard

import akka.actor.Actor
import akka.cluster.ddata.DistributedData

class InteractionQuestboard extends Actor {

  val replicator = DistributedData(context.system).replicator

  def receive: Receive = {
    case InteractionQuestboardProtocol.PostQuest(namespace, guild) =>
      ???

    case InteractionQuestboardProtocol.GetQuest(namespace) =>
      ???

    case InteractionQuestboardProtocol.RemoveQuest(namespace, guild) =>
      ???
  }
}
