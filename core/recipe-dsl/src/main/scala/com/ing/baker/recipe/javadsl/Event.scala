package com.ing.baker.recipe.javadsl

import com.ing.baker.recipe.common

case class Event(val eventClass: Class[_], override val maxFiringLimit: Option[Int]) extends common.Event {
  override val name: String = eventClass.getSimpleName
  override val providedIngredients: Seq[common.Ingredient] =
    eventClass.getDeclaredFields
      .filter(field => !field.isSynthetic)
      .map(f => createIngredient(f.getName, parseType(f.getGenericType, s"Unsupported type for ingredient '${f.getName}' on event '${eventClass.getSimpleName}'")))
}
