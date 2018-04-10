package com.ing.baker.runtime.core.interations

import com.ing.baker.il.petrinet.InteractionTransition

/**
  * The InteractionManager is responsible for all implementation of interactions.
  * It knows all available implementations and gives the correct implementation for an Interaction
  * @param interactionImplementations All
  */
class InteractionManager(private var interactionImplementations: Seq[InteractionImplementation] = Seq.empty) {

  /**
    * Add an implementation to the InteractionManager
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
    * @param interaction The interaction to check
    * @return An option containing the implementation if available
    */
  def getImplementation(interaction: InteractionTransition[_]) : Option[InteractionImplementation] =
    interactionImplementations.find(implementation => isCompatibleImplementation(interaction, implementation))

  /**
    * Checks if an implementation is available for the given interaction.
    * It check:
    *   1. Name
    *   2. Input variable sizes
    *   3. Input variable types
    * @param interaction The interaction to check
    * @return if an implementation is avaiable
    */
  def hasImplementation(interaction: InteractionTransition[_]): Boolean =
    interactionImplementations.exists(implementation => isCompatibleImplementation(interaction, implementation))

  private def isCompatibleImplementation(interaction: InteractionTransition[_], implementation: InteractionImplementation): Boolean = {
    interaction.originalInteractionName == implementation.name &&
      implementation.inputTypes.size == interaction.requiredIngredients.size &&
      implementation.inputTypes.zip(interaction.requiredIngredients.map(_.`type`)).forall {
        case (typeA, typeB) => typeA.isAssignableFrom(typeB)
      }
  }
}
