package com.ing.baker.runtime.core.internal

import java.util.concurrent.ConcurrentHashMap

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.core.InteractionImplementation

import scala.compat.java8.FunctionConverters._

/**
  * The InteractionManager is responsible for all implementation of interactions.
  * It knows all available implementations and gives the correct implementation for an Interaction
  *
  * @param interactionImplementations All
  */
class InteractionManager(private var interactionImplementations: Seq[InteractionImplementation] = Seq.empty) {

  private val implementationCache: ConcurrentHashMap[InteractionTransition, InteractionImplementation] =
    new ConcurrentHashMap[InteractionTransition, InteractionImplementation]

  private def isCompatibleImplementation(interaction: InteractionTransition, implementation: InteractionImplementation): Boolean = {
    interaction.originalInteractionName == implementation.name &&
      implementation.inputTypes.size == interaction.requiredIngredients.size &&
      implementation.inputTypes.zip(interaction.requiredIngredients.map(_.`type`)).forall {
        case (typeA, typeB) => typeA.isAssignableFrom(typeB)
      }
  }

  private def findInteractionImplementation(interaction: InteractionTransition): InteractionImplementation =
      interactionImplementations.find(implementation => isCompatibleImplementation(interaction, implementation)).orNull

  /**
    * Add an implementation to the InteractionManager
    *
    * @param implementation
    */
  def addImplementation(implementation: InteractionImplementation) =
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
  def getImplementation(interaction: InteractionTransition): Option[InteractionImplementation] =
    Option(implementationCache.computeIfAbsent(interaction, (findInteractionImplementation _).asJava))
}
