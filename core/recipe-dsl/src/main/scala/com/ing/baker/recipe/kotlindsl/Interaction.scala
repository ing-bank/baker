package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.InteractionDescriptor
import com.ing.baker.types.{Converters, Value}

import scala.collection.compat.immutable.ArraySeq
import scala.jdk.CollectionConverters._
import scala.collection.immutable.Seq
import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

class Interaction private(
  nameInput: String,
  originalNameInput: String,
  inputIngredientsInput: Seq[common.Ingredient],
  eventsInput: Seq[common.Event],
  requiredEventsInput: Set[String],
  requiredOneOfEventsInput: Set[Set[String]],
  predefinedIngredientsInput: Map[String, Value],
  overriddenIngredientNamesInput: Map[String, String],
  eventOutputTransformersInput: Map[common.Event, common.EventOutputTransformer],
  maximumInteractionCountInput: Option[Int],
  failureStrategyInput: Option[common.InteractionFailureStrategy]
) extends common.InteractionDescriptor {

  override val name: String = nameInput
  override val originalName: String = originalNameInput
  override val inputIngredients: Seq[common.Ingredient] = inputIngredientsInput
  override val output: Seq[common.Event] = eventsInput
  override val requiredEvents: Set[String] = requiredEventsInput
  override val requiredOneOfEvents: Set[Set[String]] = requiredOneOfEventsInput
  override val predefinedIngredients: Map[String, Value] = predefinedIngredientsInput
  override val overriddenIngredientNames: Map[String, String] = overriddenIngredientNamesInput
  override val overriddenOutputIngredientName: Option[String] = None
  override val eventOutputTransformers: Map[common.Event, common.EventOutputTransformer] = eventOutputTransformersInput
  override val maximumInteractionCount: Option[Int] = maximumInteractionCountInput
  override val failureStrategy: Option[common.InteractionFailureStrategy] = failureStrategyInput
}

object Interaction {
  def of(name: String,
         interactionDescriptor: InteractionDescriptor,
         requiredEvents: java.util.Set[String],
         requiredOneOfEvents: java.util.Set[java.util.Set[String]],
         predefinedIngredients: java.util.Map[String, Object],
         overriddenIngredientNames: java.util.Map[String, String],
         eventOutputTransformers: java.util.Map[Event, EventOutputTransformer],
         maximumInteractionCount: java.util.Optional[Int],
         failureStrategy: java.util.Optional[common.InteractionFailureStrategy]) = new Interaction(
    name,
    interactionDescriptor.originalName,
    interactionDescriptor.inputIngredients,
    interactionDescriptor.output,
    requiredEvents.asScala.toSet,
    requiredOneOfEvents.asScala.map(x => x.asScala.toSet).toSet,
    predefinedIngredients.asScala.toMap.map { case (k, v) => k -> Converters.toValue(v) },
    overriddenIngredientNames.asScala.toMap,
    eventOutputTransformers.asScala.toMap.map { case (k, v) => k -> v },
    maximumInteractionCount.map[Option[Int]](Option.apply(_)).orElse(None),
    failureStrategy.map[Option[InteractionFailureStrategy]](Option.apply(_)).orElse(None)
  )

  def of(name: String,
         originalName: String,
         inputIngredients: java.util.Set[Ingredient],
         events: java.util.Set[Event],
         requiredEvents: java.util.Set[String],
         requiredOneOfEvents: java.util.Set[java.util.Set[String]],
         predefinedIngredients: java.util.Map[String, Object],
         overriddenIngredientNames: java.util.Map[String, String],
         eventOutputTransformers: java.util.Map[Event, EventOutputTransformer],
         maximumInteractionCount: java.util.Optional[Int],
         failureStrategy: java.util.Optional[common.InteractionFailureStrategy]) = new Interaction(
    name,
    originalName,
    new ArraySeq.ofRef(inputIngredients.asScala.toArray),
    new ArraySeq.ofRef(events.asScala.toArray),
    requiredEvents.asScala.toSet,
    requiredOneOfEvents.asScala.map(x => x.asScala.toSet).toSet,
    predefinedIngredients.asScala.toMap.map { case (k, v) => k -> Converters.toValue(v) },
    overriddenIngredientNames.asScala.toMap,
    eventOutputTransformers.asScala.toMap.map { case (k, v) => k -> v },
    maximumInteractionCount.map[Option[Int]](Option.apply(_)).orElse(None),
    failureStrategy.map[Option[InteractionFailureStrategy]](Option.apply(_)).orElse(None)
  )
}
