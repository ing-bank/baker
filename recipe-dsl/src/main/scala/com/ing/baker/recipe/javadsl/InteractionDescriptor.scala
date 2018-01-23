package com.ing.baker.recipe.javadsl

import com.ing.baker.recipe.common
import com.ing.baker.types.Converters

import scala.annotation.varargs
import scala.collection.JavaConverters._

case class InteractionDescriptor private(
                                          override val interaction: common.Interaction,
                                          override val requiredEvents: Set[String],
                                          override val requiredOneOfEvents: Set[Set[String]],
                                          override val predefinedIngredients: Map[String, com.ing.baker.types.Value],
                                          override val overriddenIngredientNames: Map[String, String],
                                          override val overriddenOutputIngredientName: Option[String] = Option.empty[String],
                                          override val maximumInteractionCount: Option[Int],
                                          override val failureStrategy: Option[common.InteractionFailureStrategy] = None,
                                          override val eventOutputTransformers: Map[common.Event, common.EventOutputTransformer] = Map.empty,
                                          newName: String = null)
  extends common.InteractionDescriptor {

  override val name: String = {
    if (newName != null) newName
    else interaction.name
  }

  /**
    * This sets a requirement for this interaction that a specific event needs to have been fired before it can execute.
    *
    * @param newRequiredEvent the class of the events that needs to have been fired
    * @return
    */
  def withRequiredEvent(newRequiredEvent: Class[_]): InteractionDescriptor =
    this.copy(requiredEvents = requiredEvents + newRequiredEvent.getSimpleName)

  /**
    * This sets a requirement for this interaction that some specific events needs to have been fired before it can execute.
    *
    * @param newRequiredEvents the classes of the events.
    * @return
    */
  @SafeVarargs
  @varargs
  def withRequiredEvents(newRequiredEvents: Class[_]*): InteractionDescriptor =
    this.copy(requiredEvents = requiredEvents ++ newRequiredEvents.map(_.getSimpleName))

  /**
    * This sets a requirement for this interaction that some specific events needs to have been fired before it can execute.
    *
    * @param newRequiredEvents the classes of the event.
    * @return
    */
  def withRequiredEvents(newRequiredEvents: java.util.Set[Class[_]]): InteractionDescriptor =
    this.copy(requiredEvents = requiredEvents ++ newRequiredEvents.asScala.map(_.getSimpleName))


  /**
    * This sets a requirement for this interaction that a specific event needs to have been fired before it can execute.
    *
    * @param newRequiredEventName the name of the events that needs to have been fired
    * @return
    */
  def withRequiredEventFromName(newRequiredEventName: String): InteractionDescriptor =
    this.copy(requiredEvents = requiredEvents + newRequiredEventName)

  /**
    * This sets a requirement for this interaction that some specific events needs to have been fired before it can execute.
    *
    * @param newRequiredEventNames the names of the events.
    * @return
    */
  @SafeVarargs
  @varargs
  def withRequiredEventsFromName(newRequiredEventNames: String*): InteractionDescriptor =
    this.copy(requiredEvents = requiredEvents ++ newRequiredEventNames)

  /**
    * This sets a requirement for this interaction that some specific events needs to have been fired before it can execute.
    *
    * @param newRequiredEvents the names of the events.
    * @return
    */
  def withRequiredEventsFromName(newRequiredEvents: java.util.Set[String]): InteractionDescriptor =
    this.copy(requiredEvents = requiredEvents ++ newRequiredEvents.asScala)

  /**
    * This sets a requirement for this interaction that one of the given events needs to have been fired before it can execute.
    *
    * @param newRequiredOneOfEvents the classes of the events.
    * @return
    */
  @SafeVarargs
  @varargs
  def withRequiredOneOfEvents(newRequiredOneOfEvents: Class[_]*): InteractionDescriptor = {
    if (newRequiredOneOfEvents.nonEmpty && newRequiredOneOfEvents.size < 2)
      throw new IllegalArgumentException("At least 2 events should be provided as 'requiredOneOfEvents'")

    val newRequired: Set[Set[String]] = requiredOneOfEvents + newRequiredOneOfEvents.map(_.getSimpleName).toSet

    copy(requiredOneOfEvents = newRequired)
  }
//ipv assign, toevoegen in deze functie
  /**
    * This sets a requirement for this interaction that one of the given events needs to have been fired before it can execute.
    *
    * @param newRequiredOneOfEvents the names of the events.
    * @return
    */
  @SafeVarargs
  @varargs
  def withRequiredOneOfEventsFromName(newRequiredOneOfEvents: String*): InteractionDescriptor = {
    if (newRequiredOneOfEvents.nonEmpty && newRequiredOneOfEvents.size < 2)
      throw new IllegalArgumentException("At least 2 events should be provided as 'requiredOneOfEvents'")
    val newRequired: Set[Set[String]] = requiredOneOfEvents + newRequiredOneOfEvents.toSet

    copy(requiredOneOfEvents = newRequired)
  }

  /**
    * This sets a input ingredient to a set value. In this case the ingredient wont be taken from the runtime recipe.
    *
    * @param ingredientName  the name of the ingredient
    * @param ingredientValue the value of the ingredient
    * @return
    */
  def withPredefinedIngredient(ingredientName: String,
                               ingredientValue: AnyRef): InteractionDescriptor =
    addPredefinedIngredient(Map(ingredientName -> ingredientValue))

  /**
    * This sets two input ingredient to a set value. In this case the ingredients wont be taken from the runtime recipe.
    *
    * @param ingredientName1  the name of the first ingredient
    * @param ingredientValue1 the value of first the ingredient
    * @param ingredientName2  the name of the second ingredient
    * @param ingredientValue2 the value of second the ingredient
    * @return
    */
  def withPredefinedIngredients(ingredientName1: String,
                                ingredientValue1: AnyRef,
                                ingredientName2: String,
                                ingredientValue2: AnyRef): InteractionDescriptor =
    addPredefinedIngredient(
      Map(ingredientName1 -> ingredientValue1, ingredientName2 -> ingredientValue2))

  /**
    * This sets three input ingredient to a set value. In this case the ingredients wont be taken from the runtime recipe.
    *
    * @param ingredientName1  the name of the first ingredient
    * @param ingredientValue1 the value of first the ingredient
    * @param ingredientName2  the name of the second ingredient
    * @param ingredientValue2 the value of second the ingredient
    * @param ingredientName3  the name of third the ingredient
    * @param ingredientValue3 the value of third the ingredient
    * @return
    */
  def withPredefinedIngredients(ingredientName1: String,
                                ingredientValue1: AnyRef,
                                ingredientName2: String,
                                ingredientValue2: AnyRef,
                                ingredientName3: String,
                                ingredientValue3: AnyRef): InteractionDescriptor =
    addPredefinedIngredient(
      Map(ingredientName1 -> ingredientValue1,
        ingredientName2 -> ingredientValue2,
        ingredientName3 -> ingredientValue3))

  /**
    * This sets input ingredients to set values. In this case the ingredients wont be taken from the runtime recipe.
    *
    * @param newPredefinedIngredients The map containing ingredientName and ingredientValue for ingredients you want to set
    * @return
    */
  def withPredefinedIngredients(newPredefinedIngredients: java.util.Map[String, AnyRef]): InteractionDescriptor =
    addPredefinedIngredient(newPredefinedIngredients.asScala.toMap)

  private def addPredefinedIngredient(params: Map[String, AnyRef]): InteractionDescriptor =
    this.copy(predefinedIngredients = predefinedIngredients ++ params.map{case (key, value) => key -> Converters.toValue(value)})

  /**
    * This renames the ingredient that is created by this interaction
    *
    * @param newIngredientName the new ingredient name
    * @return
    */
  def renameProvidedIngredient(newIngredientName: String): InteractionDescriptor =
    this.copy(overriddenOutputIngredientName = Some(newIngredientName))

  /**
    * This renames a input ingredient
    *
    * @param oldIngredientName the name of the input ingredient you want to rename
    * @param newIngredientName the new name for the ouput ingredient
    * @return
    */
  def renameRequiredIngredient(oldIngredientName: String,
                               newIngredientName: String): InteractionDescriptor =
    this.copy(
      overriddenIngredientNames = overriddenIngredientNames + (oldIngredientName -> newIngredientName))

  /**
    * This renames the given input ingredients
    *
    * @param newOverriddenIngredients a map containing old and new names for input ingredients
    * @return new InteractionDescriptor with new ingredient names
    */
  def renameRequiredIngredients(newOverriddenIngredients: java.util.Map[String, String]): InteractionDescriptor = {
    this.copy(overriddenIngredientNames = overriddenIngredientNames ++ newOverriddenIngredients.asScala.toMap)
  }

  def withEventTransformation(eventClazz: Class[_],
                              newEventName: String,
                              ingredientRenames: java.util.Map[String, String]): InteractionDescriptor = {
    withEventTransformation(eventClazz, newEventName, ingredientRenames.asScala.toMap)
  }

  def withEventTransformation(eventClazz: Class[_],
                              newEventName: String): InteractionDescriptor = {
    withEventTransformation(eventClazz, newEventName, Map.empty[String, String])
  }

  private def withEventTransformation(eventClazz: Class[_],
                                      newEventName: String,
                                      ingredientRenames: Map[String, String]): InteractionDescriptor = {
    val originalEvent: common.Event = eventClassToCommonEvent(eventClazz, None)
    interaction.output match {
      case common.FiresOneOfEvents(events@_*) =>
        if (!events.contains(originalEvent))
          throw new common.RecipeValidationException(s"Event transformation given for Interaction $name but does not fire event $originalEvent")
      case _ => throw new common.RecipeValidationException(s"Event transformation given for Interaction $name but does not fire any event")
    }

    val eventOutputTransformer = EventOutputTransformer(newEventName, ingredientRenames)
    this.copy(eventOutputTransformers = eventOutputTransformers + (originalEvent -> eventOutputTransformer))
  }

  def withFailureStrategy(interactionFailureStrategy: common.InteractionFailureStrategy): InteractionDescriptor = {
    this.copy(failureStrategy = Some(interactionFailureStrategy))
  }

  /**
    * This actives the incremental backup retry strategy for this interaction if failure occurs
    *
    * @param initialDelay the initial delay before the first retry starts
    * @param deadline     the deadline for how long the retry should run
    * @return
    * @deprecated replace by withFailureStrategy
    */
  @Deprecated
  def withIncrementalBackoffOnFailure(initialDelay: java.time.Duration,
                                      deadline: java.time.Duration): InteractionDescriptor =
  this.copy(
    failureStrategy = Some(
      InteractionFailureStrategy.RetryWithIncrementalBackoff(
        initialDelay,
        deadline)))

  /**
    * This actives the incremental backup retry strategy for this interaction if failure occurs
    *
    * @param initialDelay          the initial delay before the first retry starts
    * @param deadline              the deadline for how long the retry should run
    * @param maxTimeBetweenRetries the max time that we will wait between duration
    * @return
    * @deprecated replace by withFailureStrategy
    */
  @Deprecated
  def withIncrementalBackoffOnFailure(initialDelay: java.time.Duration,
                                      deadline: java.time.Duration,
                                      maxTimeBetweenRetries: java.time.Duration): InteractionDescriptor =
  this.copy(
    failureStrategy = Some(
      InteractionFailureStrategy.RetryWithIncrementalBackoff(
        initialDelay,
        deadline,
        maxTimeBetweenRetries)))

  /**
    * Sets the maximum amount of times this interaction can be fired.
    *
    * @param times maximum amount of times this interaction can be fired
    * @return
    */
  def withMaximumInteractionCount(times: Int): InteractionDescriptor =
    this.copy(maximumInteractionCount = Some(times))
}

object InteractionDescriptor {
  def of[T <: Interaction](interactionClass: Class[T]): InteractionDescriptor = {
    InteractionDescriptor(interactionClassToCommonInteraction(interactionClass), Set.empty, Set.empty, Map.empty, Map.empty, None, None)
  }

  def of[T <: Interaction](interactionClass: Class[T], name: String): InteractionDescriptor = {
    InteractionDescriptor(
      interactionClassToCommonInteraction(interactionClass),
      Set.empty,
      Set.empty,
      Map.empty,
      Map.empty,
      None,
      None,
      newName = name)
  }
}
