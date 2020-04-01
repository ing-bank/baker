package com.ing.baker.runtime.akka.internal

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance}

import scala.concurrent.{ExecutionContext, Future}

/** The InteractionManager is responsible for all implementation of interactions.
  * It knows all available implementations and gives the correct implementation for an Interaction
  */
trait InteractionManager {

  /** Adds an interaction instance to the manager.
    *
    * @param interaction to be added
    * @return async writing process
    */
  def addImplementation(interaction: InteractionInstance): Future[Unit]

  /** Gets an implementation is available for the given interaction.
    * It checks:
    *   1. Name
    *   2. Input variable sizes
    *   3. Input variable types
    *
    * @param interaction The interaction to check
    * @return An option containing the implementation if available
    */
  def getImplementation(interaction: InteractionTransition): Future[Option[InteractionInstance]]

  /** Checks if an InteractionInstance in the manager matches the transition. */
  def hasImplementation(interaction: InteractionTransition)(implicit ec: ExecutionContext): Future[Boolean] =
    getImplementation(interaction).map(_.isDefined)

  /** Tries to find InteractionInstance that can run the given transition with provided input. */
  def executeImplementation(interaction: InteractionTransition, input: Seq[IngredientInstance])(implicit ec: ExecutionContext): Future[Option[EventInstance]] = {
    getImplementation(interaction).flatMap {
      case Some(implementation) => implementation.run(input)
      case None => Future.failed(new FatalInteractionException(s"No implementation available for interaction ${interaction.interactionName}"))
    }
  }

  /** Helper function for implementations of the InteractionManager, this is the core logic for the binding of
    * InteractionInstances.
    */
  protected def isCompatibleImplementation(interaction: InteractionTransition, implementation: InteractionInstance): Boolean = {
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
}
