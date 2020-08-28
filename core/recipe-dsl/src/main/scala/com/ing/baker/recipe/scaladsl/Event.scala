package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.{common, javadsl}
import com.ing.baker.types.mirror

import scala.language.experimental.macros
import scala.reflect.runtime.universe.TypeTag

object Event {

  def apply(ingredients: common.Ingredient*) : Event = macro CommonMacros.eventImpl

  def apply(name: String, ingredients: common.Ingredient*) : Event = new Event(name, ingredients, Some(1))

  def apply[T : TypeTag]: common.Event = {
    val runtimeClass = mirror.runtimeClass(mirror.typeOf[T])
    javadsl.eventClassToCommonEvent(runtimeClass, None)
  }
}

case class Event (override val name: String,
                  override val providedIngredients: Seq[common.Ingredient],
                  override val maxFiringLimit: Option[Int]) extends common.Event {
  def withMaxFiringLimit(firingLimit: Int): Event = {
    Event(this.name, this.providedIngredients, Some(firingLimit))
  }
}