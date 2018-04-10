package com.ing.baker.runtime.core.interations

import com.ing.baker.il.petrinet.InteractionTransition

class InteractionManager(private var interactionImplementations: Seq[InteractionImplementation] = Seq.empty) {

  def add(interactionImplementation: InteractionImplementation) =
    interactionImplementations :+= interactionImplementation

  def get(interactionTransition: InteractionTransition[_]) : Option[InteractionImplementation] =
    interactionImplementations.find(_.name == interactionTransition.originalInteractionName)

  def hasCompatibleImplementation(interaction: InteractionTransition[_]): Boolean =
    get(interaction).exists(implementation =>
      implementation.inputTypes.size == interaction.requiredIngredients.size &&
        implementation.inputTypes.zip(interaction.requiredIngredients.map(_.`type`)).forall {
          case (typeA, typeB) => typeA.isAssignableFrom(typeB)
        })
}
