package com.ing.baker.runtime.core.interations

import java.util.concurrent.ConcurrentHashMap

import com.ing.baker.il.petrinet.InteractionTransition

/**
  * The InteractionManager is responsible for all implementation of interactions.
  * It knows all available implementations and gives the correct implementation for an Interaction
  *
  * @param interactionImplementations All
  */
class InteractionManager(private var interactionImplementations: Seq[InteractionImplementation] = Seq.empty) {


  private val cache: ConcurrentHashMap[InteractionTransition[_], InteractionImplementation] =
    new ConcurrentHashMap[InteractionTransition[_], InteractionImplementation]

  private def isCompatibleImplementation(interaction: InteractionTransition[_], implementation: InteractionImplementation): Boolean = {
    interaction.originalInteractionName == implementation.name &&
      implementation.inputTypes.size == interaction.requiredIngredients.size &&
      implementation.inputTypes.zip(interaction.requiredIngredients.map(_.`type`)).forall {
        case (typeA, typeB) => typeA.isAssignableFrom(typeB)
      }
  }

  private val absentMethod = new java.util.function.Function[InteractionTransition[_], InteractionImplementation]() {
    override def apply(interaction: InteractionTransition[_]): InteractionImplementation = {
      interactionImplementations.find(implementation => isCompatibleImplementation(interaction, implementation)).orNull
    }
  }

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
  def getImplementation(interaction: InteractionTransition[_]): Option[InteractionImplementation] =
    Option(cache.computeIfAbsent(interaction, absentMethod))
}
