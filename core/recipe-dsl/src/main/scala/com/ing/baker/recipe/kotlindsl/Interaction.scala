package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.javadsl.InteractionDescriptor
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
  def this(
      nameInput: String,
      inputIngredientsInput: java.util.Set[Ingredient],
      eventsInput: java.util.Set[Event],
      requiredEventsInput: java.util.Set[String],
      requiredOneOfEventsInput: java.util.Set[java.util.Set[String]],
      predefinedIngredientsInput: java.util.Map[String, Object],
      overriddenIngredientNamesInput: java.util.Map[String, String],
      eventOutputTransformersInput: java.util.Map[Event, EventOutputTransformer],
      maximumInteractionCountInput: java.util.Optional[Int],
      failureStrategyInput: java.util.Optional[common.InteractionFailureStrategy]
    ) = {
      this(
        nameInput,
        nameInput,
        new ArraySeq.ofRef(inputIngredientsInput.asScala.toArray),
        new ArraySeq.ofRef(eventsInput.asScala.toArray),
        requiredEventsInput.asScala.toSet,
        requiredOneOfEventsInput.asScala.map(x => x.asScala.toSet).toSet,
        predefinedIngredientsInput.asScala.toMap.map{case(k, v) => k -> Converters.toValue(v)},
        overriddenIngredientNamesInput.asScala.toMap,
        eventOutputTransformersInput.asScala.toMap.map{case(k, v) => k -> v},
        maximumInteractionCountInput.map[Option[Int]](Option.apply(_)).orElse(None),
        failureStrategyInput.map[Option[InteractionFailureStrategy]](Option.apply(_)).orElse(None)
      )
    }

    def this(
              nameInput: String,
              interactionDescriptor: InteractionDescriptor,
              requiredEventsInput: java.util.Set[String],
              requiredOneOfEventsInput: java.util.Set[java.util.Set[String]],
              predefinedIngredientsInput: java.util.Map[String, Object],
              overriddenIngredientNamesInput: java.util.Map[String, String],
              eventOutputTransformersInput: java.util.Map[Event, EventOutputTransformer],
              maximumInteractionCountInput: java.util.Optional[Int],
              failureStrategyInput: java.util.Optional[common.InteractionFailureStrategy]
            ) = {
      this(
        nameInput,
        nameInput,
        interactionDescriptor.inputIngredients,
        interactionDescriptor.output,
        requiredEventsInput.asScala.toSet,
        requiredOneOfEventsInput.asScala.map(x => x.asScala.toSet).toSet,
        predefinedIngredientsInput.asScala.toMap.map { case (k, v) => k -> Converters.toValue(v) },
        overriddenIngredientNamesInput.asScala.toMap,
        eventOutputTransformersInput.asScala.toMap.map { case (k, v) => k -> v },
        maximumInteractionCountInput.map[Option[Int]](Option.apply(_)).orElse(None),
        failureStrategyInput.map[Option[InteractionFailureStrategy]](Option.apply(_)).orElse(None)
      )
    }
}
