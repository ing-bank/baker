package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.types.{Converters, Value}

import scala.collection.compat.immutable.ArraySeq

import scala.jdk.CollectionConverters._
import scala.collection.immutable.Seq
import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

class Interaction (
  nameInput:String,
  inputIngredientsInput: java.util.Set[Ingredient],
  eventsInput: java.util.Set[Event],
  requiredEventsInput: java.util.Set[String],
  requiredOneOfEventsInput: java.util.Set[java.util.Set[String]],
  predefinedIngredientsInput: java.util.Map[String, Object],
  overriddenIngredientNamesInput: java.util.Map[String, String],
  eventOutputTransformersInput: java.util.Map[Event, EventOutputTransformer],
  maximumInteractionCountInput: java.util.Optional[Int],
  failureStrategyInput: java.util.Optional[common.InteractionFailureStrategy],
) extends common.InteractionDescriptor {
  override val name: String = nameInput
  override val originalName: String = nameInput
  override val inputIngredients: Seq[common.Ingredient] = new ArraySeq.ofRef(inputIngredientsInput.asScala.toArray)
  override val output: Seq[Event] = new ArraySeq.ofRef(eventsInput.asScala.toArray)
  override val requiredEvents: Set[String] = requiredEventsInput.asScala.toSet
  override val requiredOneOfEvents: Set[Set[String]] = requiredOneOfEventsInput.asScala.map(x => x.asScala.toSet).toSet
  override val predefinedIngredients: Map[String, Value] = predefinedIngredientsInput.asScala.toMap.map{case(k, v) => k -> Converters.toValue(v)}
  override val overriddenIngredientNames: Map[String, String] = overriddenIngredientNamesInput.asScala.toMap
  override val overriddenOutputIngredientName: Option[String] = None
  override val eventOutputTransformers: Map[common.Event, common.EventOutputTransformer] = eventOutputTransformersInput.asScala.toMap
  override val maximumInteractionCount: Option[Int] = maximumInteractionCountInput.map[Option[Int]](Option.apply(_)).orElse(None)
  override val failureStrategy: Option[common.InteractionFailureStrategy] = failureStrategyInput.map[Option[InteractionFailureStrategy]](Option.apply(_)).orElse(None)
}
