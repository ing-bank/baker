package com.ing.baker.runtime.akka.actor.interaction_scheduling

import java.util.UUID

import akka.actor.{Actor, ActorRef, PoisonPill, Props}
import akka.cluster.pubsub.{DistributedPubSub, DistributedPubSubMediator}
import akka.util.Timeout
import com.ing.baker.runtime.akka.actor.interaction_scheduling.QuestMandated.{ComputationTimeout, PostTimeout, Start}
import com.ing.baker.runtime.scaladsl.IngredientInstance
import org.slf4j.LoggerFactory
import QuestMandated._
import com.ing.baker.baas.protocol.{ProtocolInteractionExecution, ProtocolPushPullMatching, ProtocolQuestCommit}

object QuestMandated {

  case object Start

  case object PostTimeout

  case object ComputationTimeout

  def apply(ingredients: Seq[IngredientInstance], interactionName: String, postTimeout: Timeout, computationTimeout: Timeout): Props =
    Props(new QuestMandated(UUID.randomUUID(), ingredients, interactionName, postTimeout, computationTimeout))

  private val log = LoggerFactory.getLogger(classOf[QuestMandated])
}

class QuestMandated(uuid: UUID, ingredients: Seq[IngredientInstance], interactionName: String, postTimeout: Timeout, computationTimeout: Timeout) extends Actor {

  val mediator: ActorRef = DistributedPubSub(context.system).mediator

  val pullTopic: String =
    ProtocolPushPullMatching.pullTopic(interactionName)

  val pushTopic: String =
    ProtocolPushPullMatching.pushTopic(interactionName)

  def push(): Unit =
    mediator ! DistributedPubSubMediator.Publish(pushTopic, ProtocolPushPullMatching.Push(self, uuid))

  def start(): Unit = {
    mediator ! DistributedPubSubMediator.Subscribe(pullTopic, self)
    push()
    context.system.scheduler.scheduleOnce(postTimeout.duration, self, PostTimeout)(context.dispatcher, self)
  }


  def receive: Receive = {
    case Start =>
      log.info(s"$interactionName:$uuid: Starting Quest for interaction")
      start()
      context.become(running(sender))
  }

  def running(manager: ActorRef): Receive = {
    case ProtocolPushPullMatching.Pull(agent) =>
      // respond with available quest
      log.info(s"$interactionName:$uuid: responding to pull of available agent")
      agent ! ProtocolPushPullMatching.AvailableQuest(self, uuid)

    case ProtocolQuestCommit.Considering(agent) =>
      log.info(s"$interactionName:$uuid: Mandate Quest for agent: $agent")
      // start the interaction execution protocol by responding with a commit message
      agent ! ProtocolQuestCommit.Commit(self, ProtocolInteractionExecution.ExecuteInstance(ingredients))
      context.system.scheduler.scheduleOnce(computationTimeout.duration, self, ComputationTimeout)(context.dispatcher, self)
      context.become(committed(manager))

    case PostTimeout =>
      log.info(s"$interactionName:$uuid: Timed out on waiting for response when trying to find agent")
      manager ! ProtocolInteractionExecution.NoInstanceFound
      self ! PoisonPill
  }

  def committed(manager: ActorRef): Receive = {

    case message: ProtocolInteractionExecution =>
      log.info(s"$interactionName:$uuid: Quest executed")
      // report and kill himself
      manager ! message
      self ! PoisonPill

    case ProtocolQuestCommit.Considering(agent) =>
      log.info(s"$interactionName:$uuid: rejecting other agent: $agent")
      agent ! ProtocolQuestCommit.QuestTaken

    case ComputationTimeout =>
      log.info(s"$interactionName:$uuid: Timed out on waiting for response of agent after commited")
      manager ! ProtocolInteractionExecution.InstanceExecutionTimedOut
      self ! PoisonPill
  }

}
