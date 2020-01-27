package com.ing.baker.baas.interaction

import akka.actor.ActorSystem
import akka.pattern.ask
import akka.util.Timeout
import com.ing.baker.baas.protocol.ProtocolInteractionExecution
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.akka.actor.interaction_scheduling.QuestMandated
import com.ing.baker.runtime.akka.actor.interaction_scheduling.QuestMandated.Start
import com.ing.baker.runtime.akka.internal.InteractionManager
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance}

import scala.concurrent.Future

class InteractionManagerKubernetes(system: ActorSystem, postTimeout: Timeout, computationTimeout: Timeout) extends InteractionManager {

  import system.dispatcher

  override def executeImplementation(interaction: InteractionTransition, input: Seq[IngredientInstance]): Future[Option[EventInstance]] = {
    val a = system.actorOf(QuestMandated(input, interaction.originalInteractionName, postTimeout, computationTimeout))
    a.ask(Start)(Timeout.durationToTimeout(postTimeout.duration + computationTimeout.duration)).flatMap {
      case ProtocolInteractionExecution.InstanceExecutedSuccessfully(result) => Future.successful(result)
      case ProtocolInteractionExecution.InstanceExecutionFailed(_) => Future.failed(new RuntimeException("Remote execution of interaction failed"))
      case ProtocolInteractionExecution.NoInstanceFound => executeImplementation(interaction, input)
      case ProtocolInteractionExecution.InstanceExecutionTimedOut() => Future.failed(new RuntimeException("Execution of interaction timed out"))
      case ProtocolInteractionExecution.InvalidExecution() => Future.failed(new RuntimeException("Execution of interaction failed because of invalid ingredient input"))
    }
  }

  override def hasImplementation(interaction: InteractionTransition): Boolean = true

  override def addImplementation(interaction: InteractionInstance): Unit =
    throw new NotImplementedError("addImplementation is not implemented for the distributed interaction manager, please deploy interactions using the baas-node-interaction library")
}
