package com.ing.baker.scala_api

import com.ing.baker.api.Event
import com.ing.baker.core.InteractionFailureStrategy.RetryWithIncrementalBackoff
import com.ing.baker.core.{ActionType, Interaction, InteractionDescriptor, InteractionFailureStrategy}

import scala.concurrent.duration.Duration
import scala.reflect.ClassTag

case class InteractionDescriptorImpl[T <: Interaction: ClassTag](
    interactionClass: Class[T],
    override val requiredEvents: Set[Class[_ <: Event]] = Set.empty,
    override val requiredOneOfEvents: Set[Class[_ <: Event]] = Set.empty,
    override val predefinedIngredients: Map[String, AnyRef] = Map.empty,
    override val overriddenIngredientNames: Map[String, String] = Map.empty,
    override val overriddenOutputIngredientName: String = null,
    override val maximumInteractionCount: Option[Int] = None,
    override val failureStrategy: Option[InteractionFailureStrategy] = None,
    override val actionType: ActionType = ActionType.InteractionAction)
    extends InteractionDescriptor[T] {

  def withRequiredEvent[C <: Event : ClassTag]: InteractionDescriptorImpl[T] =
    copy(requiredEvents = requiredEvents + implicitly[ClassTag[C]].runtimeClass.asInstanceOf[Class[C]])

  def withRequiredOneOfEvents(requiredOneOfEvents: Class[_ <: Event]*): InteractionDescriptorImpl[T] =
    copy(requiredOneOfEvents = requiredOneOfEvents.toSet)

  def withPredefinedIngredients(values: (String, AnyRef)*): InteractionDescriptorImpl[T] =
    copy(predefinedIngredients = values.toMap)

  def withPredefinedIngredients(data: Map[String, AnyRef]): InteractionDescriptorImpl[T] =
    copy(predefinedIngredients = data)

  def withMaximumInteractionCount(n: Int): InteractionDescriptorImpl[T] =
    copy(maximumInteractionCount = Some(n))

  def withOverriddenIngredientName(oldIngredient: String,
                                   newIngredient: String): InteractionDescriptorImpl[T] =
    copy(overriddenIngredientNames = overriddenIngredientNames + (oldIngredient -> newIngredient))

  def withOverriddenOutputIngredientName(
      newIngredientOutputName: String): InteractionDescriptorImpl[T] =
    copy(overriddenOutputIngredientName = newIngredientOutputName)

  def withIncrementalBackoffOnFailure(initialDelay: Duration,
                                      backoffFactor: Double = 2.0,
                                      maximumRetries: Int = 50): InteractionDescriptorImpl[T] =
    copy(
      failureStrategy =
        Some(RetryWithIncrementalBackoff(initialDelay, backoffFactor, maximumRetries)))

}

object InteractionDescriptorFactory {
  def apply[T <: Interaction: ClassTag](): InteractionDescriptorImpl[T] = {
    InteractionDescriptorImpl[T](implicitly[ClassTag[T]].runtimeClass.asInstanceOf[Class[T]])
  }
}
