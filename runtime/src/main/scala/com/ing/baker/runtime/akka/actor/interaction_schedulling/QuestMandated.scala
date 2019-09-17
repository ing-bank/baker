package com.ing.baker.runtime.akka.actor.interaction_schedulling

import akka.actor.{Actor, ActorRef, PoisonPill, Props}
import akka.cluster.pubsub.{DistributedPubSub, DistributedPubSubMediator}
import com.ing.baker.runtime.scaladsl.IngredientInstance

object QuestMandated {

  def apply(manager: ActorRef, ingredients: Seq[IngredientInstance], recipeName: String, interactionName: String, version: String = "v0"): Props =
    Props(new QuestMandated(manager, ingredients, recipeName, interactionName, version))
}

class QuestMandated(manager: ActorRef, ingredients: Seq[IngredientInstance], recipeName: String, interactionName: String, version: String) extends Actor {

  val mediator: ActorRef = DistributedPubSub(context.system).mediator

  val pullTopic: String =
    ProtocolPushPullMatching.pullTopic(recipeName, interactionName, version)

  val pushTopic: String =
    ProtocolPushPullMatching.pushTopic(recipeName, interactionName, version)

  def push(): Unit =
    mediator ! DistributedPubSubMediator.Publish(pushTopic, ProtocolPushPullMatching.Push(self))

  def start(): Unit =
    mediator ! DistributedPubSubMediator.Subscribe(pullTopic, self); push()

  start()

  def receive: Receive = {
    case ProtocolPushPullMatching.Pull(agent) =>
      // respond with available quest
      agent ! ProtocolPushPullMatching.AvailableQuest(self)

    case ProtocolQuestCommit.Considering(agent) =>
      // start the interaction execution protocol by responding with a commit message
      agent ! ProtocolQuestCommit.Commit(self, ProtocolInteractionExecution.ExecuteInstance(ingredients))
      context.become(committed)
  }

  def committed: Receive = {

    case message: ProtocolInteractionExecution =>
      // report and kill himself
      manager ! message
      self ! PoisonPill

    case ProtocolQuestCommit.Considering(agent) =>
      agent ! ProtocolQuestCommit.QuestTaken
  }

}
