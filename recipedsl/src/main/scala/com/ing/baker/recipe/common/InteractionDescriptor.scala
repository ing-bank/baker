package com.ing.baker.recipe.common

sealed trait ActionType
case object InteractionAction extends ActionType
case object SieveAction extends ActionType

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

  val actionType: ActionType

  override def toString(): String = toString("")

  def toString(appender: String): String = {
    s"""$appender${interaction.name}{
       |${appender + ""}requiredIngredients:(${interaction.inputIngredients.foldLeft("")((i, j) => s"$i$j")})
       |${interaction.output.toString(appender)}
       |${appender}requiredEvents(${requiredEvents.foldLeft("")((i, j) => s"$i\n${j.toString(appender + "  ")}")})
       |${appender}requiredOneOfEvents(${requiredOneOfEvents.foldLeft("")((i, j) => s"$i\n${j.toString(appender + "  ")}")})
       |${appender}predefinedIngredients(${predefinedIngredients})
       |${appender}overriddenIngredientNames(${overriddenIngredientNames})
       |${appender}overriddenOutputIngredientName(${overriddenOutputIngredientName})
       |${appender}maximumInteractionCount(${maximumInteractionCount})
       |${appender}failureStrategy(${failureStrategy})
       |${appender}eventOutputTransformers(${eventOutputTransformers})
       |$appender}""".stripMargin
  }
}
