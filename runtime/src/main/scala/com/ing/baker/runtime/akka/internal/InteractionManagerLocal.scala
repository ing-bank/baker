package com.ing.baker.runtime.akka.internal

import java.util.concurrent.ConcurrentHashMap

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance}

import scala.concurrent.Future
import scala.compat.java8.FunctionConverters._

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
  def addImplementation(implementation: InteractionInstance): Future[Unit] =
    Future.successful(interactionImplementations :+= implementation)

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

  def hasImplementation(interaction: InteractionTransition): Future[Boolean] =
    Future.successful(getImplementation(interaction).isDefined)

  override def executeImplementation(interaction: InteractionTransition, input: Seq[IngredientInstance]): Future[Option[EventInstance]] = {
    this.getImplementation(interaction) match {
      case Some(implementation) => implementation.run(input)
      case None => Future.failed(new FatalInteractionException("No implementation available for interaction"))
    }
  }
}
