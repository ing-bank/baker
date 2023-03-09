package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.{Event, EventOutputTransformer, Ingredient, InteractionFailureStrategy}
import com.ing.baker.types.Value

import scala.jdk.CollectionConverters._
case class Interaction (
  nameInput:String,
  inputIngredientsInput: java.util.Set[Ingredient],
  eventsInput: java.util.Set[Event],
  requiredEventsInput: java.util.Set[String],
) extends common.InteractionDescriptor {

  override val name = nameInput
  override val originalName = nameInput
  override val inputIngredients = inputIngredientsInput.asScala.toSeq
  override val output = eventsInput.asScala.toSeq
  override val requiredEvents: Set[String] = requiredEventsInput.asScala.toSet
  override val requiredOneOfEvents: Set[Set[String]] = Set.empty
  override val predefinedIngredients: Map[String, Value] = Map.empty
  override val overriddenIngredientNames: Map[String, String] = Map.empty
  override val overriddenOutputIngredientName: Option[String] = None
  override val eventOutputTransformers: Map[Event, EventOutputTransformer] = Map.empty
  override val maximumInteractionCount: Option[Int] = None
  override val failureStrategy: Option[InteractionFailureStrategy] = None
}
