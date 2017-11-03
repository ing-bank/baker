package com.ing.baker.runtime.core.interations

import java.lang.reflect.Type

import com.ing.baker.il.petrinet.InteractionTransition

trait InteractionImplementation {

  val name: String

  val requiredIngredients: Seq[Type]

  val returnType: Type

  def isValidForInteraction(interaction: InteractionTransition[_]) : Boolean

  def execute(input: Seq[Any]) : Any
}
