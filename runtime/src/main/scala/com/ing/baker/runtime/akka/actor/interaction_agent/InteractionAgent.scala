package com.ing.baker.runtime.akka.actor.interaction_agent

import akka.actor.{Actor, ActorRef, Props}
import akka.util.Timeout
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstance}

import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success}

object InteractionAgent {

  def apply(instance: InteractionInstance)(implicit timeout: Timeout): Props =
    Props(new InteractionAgent(instance))

  /**
    * Closes over the agent and manager actor references, just like the pipe pattern does, except it sends a more expressive
    * message in the case of failure.
    *
    * TODO: Handle invalid ingredients scenario
    *
    * @param agent actor reference
    * @param manager actor reference
    * @param result outcome of invoking the interaction instance
    * @param ec execution context to use
    */
  private[interaction_agent] def pipeExecutionResponse(agent: ActorRef, manager: ActorRef)(result: Future[Option[EventInstance]])(implicit ec: ExecutionContext): Unit = {
    result.onComplete {
      case Success(value) =>
        manager.tell(InteractionAgentProtocol.InstanceExecutedSuccessfully(value), agent)
      case Failure(exception) =>
        manager.tell(InteractionAgentProtocol.InstanceExecutionFailed(), agent)
    }
  }
}

class InteractionAgent(instance: InteractionInstance)(implicit timeout: Timeout) extends Actor {

  import context.dispatcher

  // TODO: Register to manager on creation

  def receive: Receive = {
    case InteractionAgentProtocol.ExecuteInstance(input) =>
      InteractionAgent.pipeExecutionResponse(self, sender)(instance.run(input))
  }
}
