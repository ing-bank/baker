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
  val requiredEvents: Set[Event]

  /**
    * A set of OR preconditions (events)
    */
  val requiredOneOfEvents: Set[Event]

  /**
    * A map of predefined parameter values, not provided from the recipe.
    */
  val predefinedIngredients: Map[Ingredient, AnyRef]

  /**
    * A map of overridden Ingredient Names for the input
    */
  val overriddenIngredientNames: Map[Ingredient, String]

  /**
    * This is used to overwrite the name used for the output ingredient
    */
  val overriddenOutputIngredientName: Option[String]

  /**
    * Indicates the maximum number of times the interaction may be called.
    */
  val maximumInteractionCount: Option[Int]

  /**
    * An optional strategy how to deal with failures. Falls back to the default strategy specified in the recipe.
    */
  val failureStrategy: Option[InteractionFailureStrategy]


  val eventOutputTransformers: Map[Class[_], EventOutputTransformer[_, _]]
}
