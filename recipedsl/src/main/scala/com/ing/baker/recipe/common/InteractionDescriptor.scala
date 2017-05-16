package com.ing.baker.recipe.common

import com.ing.baker.recipe.scaladsl.EventOutputTransformer

/**
  * An interaction is some code that requires input (ingredients) and produces output (ingredients)
  */
abstract class InteractionDescriptor[T <: Interaction] {

  def actionType: ActionType

  /**
    * The class on which the interaction method is defined.
    *
    * @return
    */
  def interactionClass: Class[T]

  /**
    * The name of the interaction
    */
  val name: String = interactionClass.getSimpleName

  /**
    * The name of the method.
    */
  val methodName: String = "apply"

  /**
    * A set of AND preconditions (events)
    */
  def requiredEvents: Set[Class[_ <: Event]]

  /**
    * A set of OR preconditions (events)
    */
  def requiredOneOfEvents: Set[Class[_ <: Event]]

  /**
    * A map of predefined parameter values, not provided from the recipe.
    */
  def predefinedIngredients: Map[String, AnyRef]

  /**
    * A map of overridden Ingredient Names for the input
    */
  def overriddenIngredientNames: Map[String, String]

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
