package com.ing.baker.recipe.javadsl

import java.util.Optional

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.EventOutputTransformer
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff

import scala.annotation.varargs
import scala.collection.JavaConverters._
import scala.concurrent.duration
import scala.concurrent.duration.Duration

case class InteractionDescriptor private(
                                          override val interaction: common.Interaction,
                                          override val requiredEvents: Set[common.Event],
                                          override val requiredOneOfEvents: Set[common.Event],
                                          override val predefinedIngredients: Map[String, AnyRef],
                                          override val overriddenIngredientNames: Map[String, String],
                                          override val overriddenOutputIngredientName: Option[String] = Option.empty[String],
                                          override val maximumInteractionCount: Option[Int],
                                          override val failureStrategy: Option[common.InteractionFailureStrategy] = None,
                                          override val eventOutputTransformers: Seq[common.EventOutputTransformer] = Seq.empty,
                                          override val actionType: common.ActionType = common.InteractionAction,
                                          newName: String = null)
  extends common.InteractionDescriptor {

  override val name: String = {
    if (newName != null) newName
    else interaction.name
  }

  def getRequiredEvents: java.util.Set[common.Event] = requiredEvents.asJava

  def getName: String = name

  def getPredefinedIngredients: java.util.Map[String, Object] = predefinedIngredients.asJava

  def getMaximumInteractionCount: Optional[Int] = maximumInteractionCount match {
    case None => Optional.empty()
    case Some(n) => Optional.of(n)
  }

  def withActionType(newActionType: common.ActionType): InteractionDescriptor =
    this.copy(actionType = newActionType)

  /**
    * This sets a requirement for this interaction that a specific event needs to have been fired before it can execute.
    *
    * @param newRequiredEvent the class of the events that needs to have been fired
    * @return
    */
  def withRequiredEvent(newRequiredEvent: Class[_ <: Event]): InteractionDescriptor =
  this.copy(requiredEvents = requiredEvents + eventClassToCommonEvent(newRequiredEvent))

  /**
    * This sets a requirement for this interaction that some specific events needs to have been fired before it can execute.
    *
    * @param newRequiredEvents the classes of the events.
    * @return
    */
  @SafeVarargs
  @varargs
  def withRequiredEvents(newRequiredEvents: Class[_ <: Event]*): InteractionDescriptor =
  this.copy(requiredEvents = requiredEvents ++ newRequiredEvents.map(eventClassToCommonEvent))

  /**
    * This sets a requirement for this interaction that some specific events needs to have been fired before it can execute.
    *
    * @param newRequiredEvents the classes of the event.
    * @return
    */
  def withRequiredEvents(newRequiredEvents: java.util.Set[Class[_ <: Event]]): InteractionDescriptor =
  this.copy(requiredEvents = requiredEvents ++ newRequiredEvents.asScala.map(eventClassToCommonEvent))

  /**
    * This sets a requirement for this interaction that one of the given events needs to have been fired before it can execute.
    *
    * @param requiredOneOfEvents the classes of the events.
    * @return
    */
  @SafeVarargs
  @varargs
  def withRequiredOneOfEvents(requiredOneOfEvents: Class[_ <: Event]*): InteractionDescriptor =
  this.copy(requiredOneOfEvents = requiredOneOfEvents.map(eventClassToCommonEvent).toSet)

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
  def withPredefinedIngredients(
                                 newPredefinedIngredients: java.util.Map[String, AnyRef]): InteractionDescriptor =
  this.copy(
    predefinedIngredients = predefinedIngredients ++ newPredefinedIngredients.asScala.toMap)

  private def addPredefinedIngredient(params: Map[String, AnyRef]): InteractionDescriptor =
    this.copy(predefinedIngredients = predefinedIngredients ++ params)

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
    * @return
    */
  def renameRequiredIngredients(
                                 newOverriddenIngredients: java.util.Map[String, String]): InteractionDescriptor =
  this.copy(
    overriddenIngredientNames = overriddenIngredientNames ++ newOverriddenIngredients.asScala.toMap)

  /**
    *
    * @param eventClazz
    * @param newEventName
    * @param ingredientRenames
    * @tparam A
    * @return
    */
  def withEventTransformation[A <: Event](
                                           eventClazz: Class[A],
                                           newEventName: String,
                                           ingredientRenames: Map[String, String]): InteractionDescriptor = {

    val originalEvent: common.Event = eventClassToCommonEvent(eventClazz)
    val fn: common.Event => common.Event = event =>
      new common.Event {
        override val name: String = newEventName
        override val providedIngredients: Seq[common.Ingredient] = event.providedIngredients.map(i =>
          new common.Ingredient {
            override val name: String = ingredientRenames.getOrElse(i.name, i.name)
            override val clazz: Class[_] = i.clazz
          })
      }
    val newEvent = fn(originalEvent)

    val eventOutputTransformer = EventOutputTransformer(originalEvent, newEvent, fn)
    this.copy(eventOutputTransformers = eventOutputTransformers :+ eventOutputTransformer)
  }

  /**
    * This actives the incremental backup retry strategy for this interaction if failure occurs
    *
    * @param initialDelay the initial delay before the first retry starts
    * @param deadline     the deadline for how long the retry should run
    * @return
    */
  def withIncrementalBackoffOnFailure(initialDelay: java.time.Duration,
                                      deadline: java.time.Duration): InteractionDescriptor =
  this.copy(
    failureStrategy = Some(
      RetryWithIncrementalBackoff(Duration(initialDelay.toMillis, duration.MILLISECONDS),
        Duration(deadline.toMillis, duration.MILLISECONDS))))

  /**
    * This actives the incremental backup retry strategy for this interaction if failure occurs
    *
    * @param initialDelay   the initial delay before the first retry starts
    * @param backoffFactor  the backoff factor for the retry
    * @param maximumRetries the maximum ammount of retries.
    * @return
    */
  def withIncrementalBackoffOnFailure(initialDelay: java.time.Duration,
                                      backoffFactor: Double,
                                      maximumRetries: Int): InteractionDescriptor =
  this.copy(
    failureStrategy = Some(
      RetryWithIncrementalBackoff(Duration(initialDelay.toMillis, duration.MILLISECONDS),
        backoffFactor,
        maximumRetries)))

  /**
    * Sets the maximum amount of times this interaction can be fired.
    *
    * @param times
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
