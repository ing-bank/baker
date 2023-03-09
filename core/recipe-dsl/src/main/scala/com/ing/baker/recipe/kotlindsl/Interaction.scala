package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.{Event, EventOutputTransformer, Ingredient, InteractionFailureStrategy}
import com.ing.baker.types.Value

import scala.jdk.CollectionConverters._
import scala.collection.immutable.Seq
import scala.collection.immutable.List

class Interaction (
  nameInput:String,
  inputIngredientsInput: java.util.Set[Ingredient],
  eventsInput: java.util.Set[Event],
  requiredEventsInput: java.util.Set[String],
) extends common.InteractionDescriptor {
  override val name: String = nameInput
  override val originalName: String = nameInput
  override val inputIngredients: Seq[Ingredient] = List.apply(inputIngredientsInput.asScala.toSeq:_*)
  override val output: Seq[Event] = List.apply(eventsInput.asScala.toSeq:_*)
  override val requiredEvents: Set[String] = requiredEventsInput.asScala.toSet
  override val requiredOneOfEvents: Set[Set[String]] = Set.empty
  override val predefinedIngredients: Map[String, Value] = Map.empty
  override val overriddenIngredientNames: Map[String, String] = Map.empty
  override val overriddenOutputIngredientName: Option[String] = None
  override val eventOutputTransformers: Map[Event, EventOutputTransformer] = Map.empty
  override val maximumInteractionCount: Option[Int] = None
  override val failureStrategy: Option[InteractionFailureStrategy] = None
}
