package com.ing.baker
package java_api

import java.util.Optional

import com.ing.baker.core.InteractionFailureStrategy._
import com.ing.baker.core.{ActionType, EventOutputTransformer, InteractionDescriptor, InteractionFailureStrategy}

import scala.annotation.varargs
import scala.collection.JavaConverters._
import scala.concurrent.duration
import scala.concurrent.duration.Duration
import scala.reflect.ClassTag

case class JInteractionDescriptor[T <: JInteraction] private (
    interactionClass: Class[T],
    requiredEvents: Set[Class[_]],
    requiredOneOfEvents: Set[Class[_]],
    predefinedIngredients: Map[String, AnyRef],
    overriddenIngredientNames: Map[String, String],
    override val overriddenOutputIngredientName: String = null,
    override val maximumInteractionCount: Option[Int],
    override val failureStrategy: Option[InteractionFailureStrategy] = None,
    override val eventOutputTransformers: Map[Class[_], EventOutputTransformer[_, _]] = Map.empty,
    override val actionType: ActionType = ActionType.InteractionAction,
    newName: String = null)
    extends InteractionDescriptor[T] {

  override val name: String = {
    if (newName != null) newName
    else interactionClass.getSimpleName
  }

  def getRequiredEvents: java.util.Set[Class[_]] = requiredEvents.asJava

  def getName: String = name

  def getInteractionClass: Class[_] = interactionClass

  def getPredefinedIngredients: java.util.Map[String, Object] = predefinedIngredients.asJava

  def getMaximumInteractionCount: Optional[Int] = maximumInteractionCount match {
    case None    => Optional.empty()
    case Some(n) => Optional.of(n)
  }

  def withActionType(newActionType: ActionType): JInteractionDescriptor[T] =
    this.copy(actionType = newActionType)

  /**
    * This sets a requirement for this interaction that a specific event needs to have been fired before it can execute.
    *
    * @param newRequiredEvent the class of the events that needs to have been fired
    * @tparam C
    * @return
    */
  def withRequiredEvent[C](newRequiredEvent: Class[C]): JInteractionDescriptor[T] =
    this.copy(requiredEvents = requiredEvents + newRequiredEvent)

  /**
    * This sets a requirement for this interaction that some specific events needs to have been fired before it can execute.
    *
    * @param newRequiredEvents the classes of the events.
    * @return
    */
  @varargs
  def withRequiredEvents(newRequiredEvents: Class[_]*): JInteractionDescriptor[T] =
    this.copy(requiredEvents = requiredEvents ++ newRequiredEvents.toSet)

  /**
    * This sets a requirement for this interaction that some specific events needs to have been fired before it can execute.
    *
    * @param newRequiredEvents the classes of the event.
    * @return
    */
  def withRequiredEvents(newRequiredEvents: java.util.Set[Class[_]]): JInteractionDescriptor[T] =
    this.copy(requiredEvents = requiredEvents ++ newRequiredEvents.asScala)

  /**
    * This sets a requirement for this interaction that one of the given events needs to have been fired before it can execute.
    *
    * @param requiredOneOfEvents the classes of the events.
    * @return
    */
  @varargs
  def withRequiredOneOfEvents(requiredOneOfEvents: Class[_]*): JInteractionDescriptor[T] =
    this.copy(requiredOneOfEvents = requiredOneOfEvents.toSet)

  /**
    * This sets a input ingredient to a set value. In this case the ingredient wont be taken from the runtime recipe.
    *
    * @param ingredientName  the name of the ingredient
    * @param ingredientValue the value of the ingredient
    * @return
    */
  def withPredefinedIngredient(ingredientName: String,
                               ingredientValue: AnyRef): JInteractionDescriptor[T] =
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
                                ingredientValue2: AnyRef): JInteractionDescriptor[T] =
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
                                ingredientValue3: AnyRef): JInteractionDescriptor[T] =
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
      newPredefinedIngredients: java.util.Map[String, AnyRef]): JInteractionDescriptor[T] =
    this.copy(
      predefinedIngredients = predefinedIngredients ++ newPredefinedIngredients.asScala.toMap)

  private def addPredefinedIngredient(params: Map[String, AnyRef]): JInteractionDescriptor[T] =
    this.copy(predefinedIngredients = predefinedIngredients ++ params)

  /**
    * This renames the ingredient that is created by this interaction
    *
    * @param newIngredientName the new ingredient name
    * @return
    */
  def renameProvidedIngredient(newIngredientName: String): JInteractionDescriptor[T] =
    this.copy(overriddenOutputIngredientName = newIngredientName)

  /**
    * This renames a input ingredient
    *
    * @param oldIngredientName the name of the input ingredient you want to rename
    * @param newIngredientName the new name for the ouput ingredient
    * @return
    */
  def renameRequiredIngredient(oldIngredientName: String,
                               newIngredientName: String): JInteractionDescriptor[T] =
    this.copy(
      overriddenIngredientNames = overriddenIngredientNames + (oldIngredientName -> newIngredientName))

  /**
    * This renames the given input ingredients
    *
    * @param newOverriddenIngredients a map containing old and new names for input ingredients
    * @return
    */
  def renameRequiredIngredients(
      newOverriddenIngredients: java.util.Map[String, String]): JInteractionDescriptor[T] =
    this.copy(
      overriddenIngredientNames = overriddenIngredientNames ++ newOverriddenIngredients.asScala.toMap)

  /**
    * Transforms the provided event for this interaction using a function.
    *
    * @param transformFunction The function that changes the event from the old to the new object
    * @param eventClazz        The class of the original event
    * @param newEventClazz     The class of the new event
    * @return
    */
  def withEventTransformation[A, B](
      eventClazz: Class[A],
      newEventClazz: Class[B],
      transformFunction: java.util.function.Function[A, B]): JInteractionDescriptor[T] = {

    import scala.compat.java8.FunctionConverters._

    implicit val eventClazzTag    = ClassTag[A](eventClazz)
    implicit val newEventClazzTag = ClassTag[B](newEventClazz)

    val fn = EventOutputTransformer[A, B](transformFunction.asScala)
    this.copy(eventOutputTransformers = eventOutputTransformers + (fn.sourceType -> fn))
  }

  /**
    * This actives the incremental backup retry strategy for this interaction if failure occurs
    *
    * @param initialDelay the initial delay before the first retry starts
    * @param deadline     the deadline for how long the retry should run
    * @return
    */
  def withIncrementalBackoffOnFailure(initialDelay: java.time.Duration,
                                      deadline: java.time.Duration): JInteractionDescriptor[T] =
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
                                      maximumRetries: Int): JInteractionDescriptor[T] =
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
  def withMaximumInteractionCount(times: Int): JInteractionDescriptor[T] =
    this.copy(maximumInteractionCount = Some(times))
}

object JInteractionDescriptor {
  def of[T <: JInteraction](clazz: Class[T]): JInteractionDescriptor[T] = {
    JInteractionDescriptor(clazz, Set.empty, Set.empty, Map.empty, Map.empty, null, None)
  }

  def of[T <: JInteraction](clazz: Class[T], name: String): JInteractionDescriptor[T] = {
    JInteractionDescriptor(clazz,
                           Set.empty,
                           Set.empty,
                           Map.empty,
                           Map.empty,
                           null,
                           None,
                           newName = name)
  }
}
