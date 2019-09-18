package com.ing.baker.runtime.akka.internal

import java.util.concurrent.ConcurrentHashMap

import akka.actor.ActorSystem
import akka.pattern.ask
import akka.util.Timeout
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.akka.actor.interaction_schedulling.QuestMandated.Start
import com.ing.baker.runtime.akka.actor.interaction_schedulling.{InteractionAgent, ProtocolInteractionExecution, QuestMandated}
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance}

import scala.compat.java8.FunctionConverters._
import scala.concurrent.Future



trait InteractionManager {
  def hasImplementation(interaction: InteractionTransition): Boolean

  def executeImplementation(interaction: InteractionTransition, input: Seq[IngredientInstance]): Future[Option[EventInstance]]

  /**
    * Add an implementation to the InteractionManager
    *
    * @param implementation
    */
  def addImplementation(implementation: InteractionInstance): Unit

}

class InteractionManagerDis(system: ActorSystem, postTimeout: Timeout, computationTimeout: Timeout) extends InteractionManager {

  import system.dispatcher

  override def executeImplementation(interaction: InteractionTransition, input: Seq[IngredientInstance]): Future[Option[EventInstance]] = {
    val a = system.actorOf(QuestMandated(input, interaction.originalInteractionName, postTimeout, computationTimeout))
    a.ask(Start)(Timeout.durationToTimeout(postTimeout.duration + computationTimeout.duration)).flatMap {
      case ProtocolInteractionExecution.InstanceExecutedSuccessfully(result) => Future.successful(result)
      case ProtocolInteractionExecution.InstanceExecutionFailed() => Future.failed(new RuntimeException("Remote execution of interaction failed"))
      case ProtocolInteractionExecution.NoInstanceFound => executeImplementation(interaction, input)
      case ProtocolInteractionExecution.InstanceExecutionTimedOut() => Future.failed(new RuntimeException("Execution of interaction timed out"))
      case ProtocolInteractionExecution.InvalidExecution() => Future.failed(new RuntimeException("Execution of interaction failed because of invalid ingredient input"))
    }
  }

  /**
    * Add an implementation to the InteractionManager
    *
    * @param implementation
    */
  override def addImplementation(implementation: InteractionInstance): Unit = {
    system.actorOf(InteractionAgent(implementation))
  }

  override def hasImplementation(interaction: InteractionTransition): Boolean = true
}

/**
  * The InteractionManager is responsible for all implementation of interactions.
  * It knows all available implementations and gives the correct implementation for an Interaction
  *
  * @param interactionImplementations All
  */
class InteractionManagerLocal(private var interactionImplementations: Seq[InteractionInstance] = Seq.empty) extends InteractionManager {

  private val implementationCache: ConcurrentHashMap[InteractionTransition, InteractionInstance] =
    new ConcurrentHashMap[InteractionTransition, InteractionInstance]

  private def isCompatibleImplementation(interaction: InteractionTransition, implementation: InteractionInstance): Boolean = {
    val interactionNameMatches =
      interaction.originalInteractionName == implementation.name
    val inputSizeMatches =
      implementation.input.size == interaction.requiredIngredients.size
    val inputNamesAndTypesMatches =
      interaction
        .requiredIngredients
        .forall { descriptor =>
          implementation.input.exists(_.isAssignableFrom(descriptor.`type`))
        }
    interactionNameMatches && inputSizeMatches && inputNamesAndTypesMatches
  }

  private def findInteractionImplementation(interaction: InteractionTransition): InteractionInstance =
      interactionImplementations.find(implementation => isCompatibleImplementation(interaction, implementation)).orNull

  /**
    * Add an implementation to the InteractionManager
    *
    * @param implementation
    */
  def addImplementation(implementation: InteractionInstance): Unit =
    interactionImplementations :+= implementation

  /**
    * Gets an implementation is available for the given interaction.
    * It checks:
    *   1. Name
    *   2. Input variable sizes
    *   3. Input variable types
    *
    * @param interaction The interaction to check
    * @return An option containing the implementation if available
    */
  private[internal] def getImplementation(interaction: InteractionTransition): Option[InteractionInstance] =
    Option(implementationCache.computeIfAbsent(interaction, (findInteractionImplementation _).asJava))

  def hasImplementation(interaction: InteractionTransition): Boolean =
    getImplementation(interaction).isDefined

  override def executeImplementation(interaction: InteractionTransition, input: Seq[IngredientInstance]): Future[Option[EventInstance]] = {
    this.getImplementation(interaction) match {
      case Some(implementation) => implementation.run(input)
      case None => Future.failed(new FatalInteractionException("No implementation available for interaction"))
    }
  }
}
