package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common

import java.lang.reflect.Type
import scala.jdk.CollectionConverters._

case class Sieve(
  nameInput: String = "",
  inputIngredientsInput: java.util.List[Ingredient],
  outputInput: java.util.List[Event],
  functionInput: Any,
  javaTypesInput: java.util.List[Type]) extends common.Sieve {
  val name: String = nameInput
  override val inputIngredients: Seq[common.Ingredient] = inputIngredientsInput.asScala.toSeq
  override val output: Seq[common.Event] = outputInput.asScala.toSeq
  override val function: Any = functionInput
  override val javaTypes: Seq[Type] = javaTypesInput.asScala.toSeq
}
