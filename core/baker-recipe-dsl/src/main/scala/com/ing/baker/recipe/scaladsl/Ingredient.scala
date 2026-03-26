package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common
import com.ing.baker.types.{Converters, Value}

import scala.language.experimental.macros
import scala.reflect.runtime.{universe => ru}

object Ingredient {
  val mirror: ru.Mirror = ru.runtimeMirror(classOf[Ingredient[_]].getClassLoader)

  def apply[T: ru.TypeTag]: Ingredient[T] = macro CommonMacros.ingredientImpl[T]
}

case class Ingredient[T : ru.TypeTag](override val name: String) extends common.Ingredient(name, Converters.readJavaType[T]) {

  def apply(value: T): (String, Value) = name -> Converters.toValue(value)
}
