package com.ing.baker.baas

import java.lang.reflect.Type

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.core.interations.InteractionImplementation

abstract class ApiInteractionImplementation extends InteractionImplementation {
  override val name: String
  override val requiredIngredients: Seq[Type]
  override val returnType: Type

  override def isValidForInteraction(interaction: InteractionTransition[_]): Boolean

  override def execute(input: Seq[Any]): Any
}
