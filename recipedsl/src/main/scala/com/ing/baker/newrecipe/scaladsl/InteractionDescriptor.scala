package com.ing.baker.newrecipe.scaladsl

import com.ing.baker.newrecipe.common
import com.ing.baker.newrecipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.EventOutputTransformer

case class InteractionDescriptor private(override val interaction: Interaction,
                                         override val requiredEvents: Set[common.Event]  = Set.empty,
                                         override val requiredOneOfEvents: Set[common.Event]  = Set.empty,
                                         override val predefinedIngredients: Map[common.Ingredient, AnyRef]  = Map.empty,
                                         override val overriddenIngredientNames: Map[common.Ingredient, String] = Map.empty,
                                         override val overriddenOutputIngredientName: Option[String] = None,
                                         override val maximumInteractionCount: Option[Int] = None,
                                         override val failureStrategy: Option[InteractionFailureStrategy] = None,
                                         override val eventOutputTransformers: Map[Class[_], EventOutputTransformer[_, _]] = Map.empty)
  extends common.InteractionDescriptor {

    def withRequiredEvent(event: Event): InteractionDescriptor =
      copy(requiredEvents = requiredEvents + event)

    def withRequiredEvents(events: Event*): InteractionDescriptor =
      copy(requiredEvents = requiredEvents ++ events)

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

  override def toString(): String = toString("")

    def toString(appender: String): String = {
      s"""$appender${interaction.name}{
         |${appender + ""} requiredIngredients:(${interaction.inputIngredients.foldLeft("")((i, j) => s"$i$j")})
         |${interaction.interactionOutput.toString(appender + "  ")}
         |$appender}""".stripMargin
  }
}

object InteractionDescriptorFactory {
  def apply(interaction: Interaction): InteractionDescriptor = InteractionDescriptor(interaction)
}
