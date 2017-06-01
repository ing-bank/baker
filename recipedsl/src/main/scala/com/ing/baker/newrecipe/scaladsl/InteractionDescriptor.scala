package com.ing.baker.newrecipe.scaladsl

import com.ing.baker.newrecipe.common
import com.ing.baker.newrecipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.EventOutputTransformer

case class InteractionDescriptor private(override val interaction: Interaction,
                                         override val requiredEvents: Set[Event]  = Set.empty,
                                         override val requiredOneOfEvents: Set[Event]  = Set.empty,
                                         override val predefinedIngredients: Map[Ingredient[_], AnyRef]  = Map.empty,
                                         override val overriddenIngredientNames: Map[Ingredient[_], String] = Map.empty,
                                         override val overriddenOutputIngredientName: Option[String] = None,
                                         override val maximumInteractionCount: Option[Int] = None,
                                         override val failureStrategy: Option[InteractionFailureStrategy] = None,
                                         override val eventOutputTransformers: Map[Class[_], EventOutputTransformer[_, _]] = Map.empty)
  extends common.InteractionDescriptor {

  //  def withRequiredEvent(event: Event): InteractionDescriptor =
  //    copy(requiredEvents = requiredEvents + event)

  //  def withRequiredOneOfEvents(requiredOneOfEvents: Class[_ <: Event]*): InteractionDescriptorImpl[T] =
  //    copy(requiredOneOfEvents = requiredOneOfEvents.toSet)
  //
  //  def withPredefinedIngredients(values: (String, AnyRef)*): InteractionDescriptorImpl[T] =
  //    copy(predefinedIngredients = values.toMap)
  //
  //  def withPredefinedIngredients(data: Map[String, AnyRef]): InteractionDescriptorImpl[T] =
  //    copy(predefinedIngredients = data)
  //
  //  def withMaximumInteractionCount(n: Int): InteractionDescriptorImpl[T] =
  //    copy(maximumInteractionCount = Some(n))
  //
  //  def withOverriddenIngredientName(oldIngredient: String,
  //                                   newIngredient: String): InteractionDescriptorImpl[T] =
  //    copy(overriddenIngredientNames = overriddenIngredientNames + (oldIngredient -> newIngredient))
  //
  //  def withOverriddenOutputIngredientName(
  //                                          newIngredientOutputName: String): InteractionDescriptorImpl[T] =
  //    copy(overriddenOutputIngredientName = newIngredientOutputName)
  //
  //  def withIncrementalBackoffOnFailure(initialDelay: Duration,
  //                                      backoffFactor: Double = 2.0,
  //                                      maximumRetries: Int = 50): InteractionDescriptorImpl[T] =
  //    copy(
  //      failureStrategy =
  //        Some(RetryWithIncrementalBackoff(initialDelay, backoffFactor, maximumRetries)))
}

object InteractionDescriptor {
  def apply(interaction: Interaction): InteractionDescriptor = InteractionDescriptor(interaction)
}
