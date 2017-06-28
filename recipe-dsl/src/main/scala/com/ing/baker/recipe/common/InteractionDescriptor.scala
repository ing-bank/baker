package com.ing.baker.recipe.common

/**
  * An interaction is some code that requires input (ingredients) and produces output (ingredients)
  */
trait InteractionDescriptor {

  val interaction: Interaction

  val name: String

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
  val predefinedIngredients: Map[String, AnyRef]

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

  override def toString(): String = {
    s"""${interaction.name}{
       |requiredIngredients:(${interaction.inputIngredients.foldLeft("")((i, j) => s"$i$j")})
       |${interaction.output.toString}
       |requiredEvents(${requiredEvents.mkString("\n")})
       |requiredOneOfEvents(${requiredOneOfEvents.mkString("\n")})
       |predefinedIngredients(${predefinedIngredients})
       |overriddenIngredientNames(${overriddenIngredientNames})
       |overriddenOutputIngredientName(${overriddenOutputIngredientName})
       |maximumInteractionCount(${maximumInteractionCount})
       |failureStrategy(${failureStrategy})
       |eventOutputTransformers(${eventOutputTransformers})""".stripMargin
  }
}