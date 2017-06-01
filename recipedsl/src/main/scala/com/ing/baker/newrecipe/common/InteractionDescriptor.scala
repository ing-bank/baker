package com.ing.baker.newrecipe.common

import com.ing.baker.recipe.common.EventOutputTransformer

/**
  * An interaction is some code that requires input (ingredients) and produces output (ingredients)
  */
trait InteractionDescriptor {

  val interaction: Interaction

  /**
    * A set of AND preconditions (events)
    */
  def requiredEvents: Set[Event]

  /**
    * A set of OR preconditions (events)
    */
  def requiredOneOfEvents: Set[Event]

  /**
    * A map of predefined parameter values, not provided from the recipe.
    */
  def predefinedIngredients: Map[Ingredient, AnyRef]

  /**
    * A map of overridden Ingredient Names for the input
    */
  def overriddenIngredientNames: Map[Ingredient, String]

  /**
    * This is used to overwrite the name used for the output ingredient
    */
  def overriddenOutputIngredientName: String

  /**
    * Indicates the maximum number of times the interaction may be called.
    */
  def maximumInteractionCount: Option[Int] = None

  /**
    * An optional strategy how to deal with failures. Falls back to the default strategy specified in the recipe.
    */
  def failureStrategy: Option[InteractionFailureStrategy] = None

  val eventOutputTransformers: Map[Class[_], EventOutputTransformer[_, _]] = Map.empty
}
