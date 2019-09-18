package com.ing.baker.runtime.akka.actor.interaction_schedulling

import akka.actor.{Actor, ActorRef, Props}
import akka.cluster.pubsub.{DistributedPubSub, DistributedPubSubMediator}
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstance}
import org.slf4j.LoggerFactory
import InteractionAgent._

import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success}

object InteractionAgent {

  def apply(instance: InteractionInstance): Props =
    Props(new InteractionAgent(instance))

  /**
    * Closes over the agent actor references, just like the pipe pattern does, except it sends a more expressive
    * message in the case of failure.
    *
    * TODO: Handle invalid ingredients scenario
    *
    * @param agent actor reference
    * @param result outcome of invoking the interaction instance
    * @param ec execution context to use
    */
  private[interaction_schedulling] def pipeBackExecutionResponse(agent: ActorRef)(result: Future[Option[EventInstance]])(implicit ec: ExecutionContext): Unit = {
    result.onComplete {
      case Success(value) =>
        agent.tell(ProtocolInteractionExecution.InstanceExecutedSuccessfully(value), agent)
      case Failure(exception) =>
        agent.tell(ProtocolInteractionExecution.InstanceExecutionFailed(), agent)
    }
  }

  private val log = LoggerFactory.getLogger(classOf[InteractionAgent])
}

class InteractionAgent(interaction: InteractionInstance) extends Actor {

  import context.dispatcher

  val mediator: ActorRef = DistributedPubSub(context.system).mediator

  val pullTopic: String =
    ProtocolPushPullMatching.pullTopic(interaction.name)

  val pushTopic: String =
    ProtocolPushPullMatching.pushTopic(interaction.name)

  def pull(): Unit =
    mediator ! DistributedPubSubMediator.Publish(pullTopic, ProtocolPushPullMatching.Pull(self))

  def subscribePush(): Unit =
    mediator ! DistributedPubSubMediator.Subscribe(pushTopic, self)

  def unsubscribePush(): Unit =
    mediator ! DistributedPubSubMediator.Unsubscribe(pushTopic, self)

  subscribePush()
  pull()

  def receive: Receive = {
    case ProtocolPushPullMatching.Push(mandated) =>
      // start Quest commit protocol
      log.info(s"${interaction.name}: Considering quest from $mandated")
      mandated ! ProtocolQuestCommit.Considering(self)
      unsubscribePush()
      context.become(considering)

    case ProtocolPushPullMatching.AvailableQuest(mandated) =>
      // start Quest commit protocol
      log.info(s"${interaction.name}: Considering quest from $mandated")
      mandated ! ProtocolQuestCommit.Considering(self)
      unsubscribePush()
      context.become(considering)
  }

  def considering: Receive = {
    case ProtocolQuestCommit.Commit(mandated, executeMessage) =>
      log.info(s"${interaction.name}: Commited to quest from $mandated")
      // start the execution protocol by already starting the computation and become committed
      InteractionAgent.pipeBackExecutionResponse(self)(interaction.run(executeMessage.input))
      context.become(committed(mandated))

    case ProtocolQuestCommit.QuestTaken =>
      log.info(s"${interaction.name}: Quest taken, starting the protocol again")
      // quest taIken, start all over again
      subscribePush()
      pull()
      context.become(receive)
  }

  def committed(mandated: ActorRef): Receive = {
    case message: ProtocolInteractionExecution =>
      log.info(s"${interaction.name}: Considering quest from $mandated")
      // Forward the result
      mandated ! message
      // Start all over again
      subscribePush()
      pull()
      context.become(receive)
  }
}
