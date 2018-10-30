package com.ing.baker.recipe.common

import com.ing.baker.types

/**
  * An interaction is some code that requires input (ingredients) and produces output (ingredients)
  */
trait InteractionDescriptor {

  /**
    * The name of the interaction.
    */
  val name: String

  /**
    * The original name of the interaction.
    */
  val originalName: String

  /**
    * The retry exhausted event name
    *
    * @return
    */
  def retryExhaustedEventName: String = this.name + exhaustedEventAppend

  /**
    * The input ingredients.
    *
    */
  val inputIngredients: Seq[Ingredient]

  /**
    * The interaction output.
    */
  val output: Seq[Event]

  /**
    * A set of names of the events AND preconditions (events)
    */
  val requiredEvents: Set[String]

  /**
    * A set of names of the events OR preconditions (events)
    */
  val requiredOneOfEvents: Set[Set[String]]

  /**
    * A map of predefined parameter values, not provided from the recipe.
    */
  val predefinedIngredients: Map[String, types.Value]

  /**
    * A map of overridden Ingredient Names for the input
    */
  val overriddenIngredientNames: Map[String, String]

  /**
    * This is used to overwrite the name used for the output ingredient
    */
  val overriddenOutputIngredientName: Option[String]

  /**
    * This is used to overwrite the name used for the output event and for the ingredients created by the event
    */
  val eventOutputTransformers: Map[Event, EventOutputTransformer]

  /**
    * Indicates the maximum number of times the interaction may be called.
    */
  val maximumInteractionCount: Option[Int]

  /**
    * An optional strategy how to deal with failures. Falls back to the default strategy specified in the recipe.
    */
  val failureStrategy: Option[InteractionFailureStrategy]
}