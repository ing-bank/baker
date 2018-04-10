package com.ing.baker.runtime.core.interations

import com.ing.baker.il.petrinet.InteractionTransition

class InteractionManager(private var interactionImplementations: Seq[InteractionImplementation] = Seq.empty) {

  def addImplementation(implementation: InteractionImplementation) =
    interactionImplementations :+= implementation

  def getImplementation(interaction: InteractionTransition[_]) : Option[InteractionImplementation] =
    interactionImplementations.find(implementation => isCompatibleImplementation(interaction, implementation))

  def hasCompatibleImplementation(interaction: InteractionTransition[_]): Boolean =
    interactionImplementations.exists(implementation => isCompatibleImplementation(interaction, implementation))

  private def isCompatibleImplementation(interaction: InteractionTransition[_], implementation: InteractionImplementation): Boolean = {
    interaction.originalInteractionName == implementation.name &&
      implementation.inputTypes.size == interaction.requiredIngredients.size &&
      implementation.inputTypes.zip(interaction.requiredIngredients.map(_.`type`)).forall {
        case (typeA, typeB) => typeA.isAssignableFrom(typeB)
      }
  }
}
