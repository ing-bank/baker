package com.ing.baker.runtime.model.recipeinstance

import com.ing.baker.il.EventDescriptor
import com.ing.baker.il.petrinet.{Place, Transition}
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.runtime.model.FireSensoryEventRejection
import com.ing.baker.runtime.model.recipeinstance.RecipeInstanceEventValidation.EventValidation
import com.ing.baker.runtime.scaladsl.EventInstance

object RecipeInstanceEventValidation {

  type Reason = String

  type EventValidation[A] =
    Either[(FireSensoryEventRejection, Reason), A]
}

trait RecipeInstanceEventValidation { recipeInstance: RecipeInstanceState =>

  def validateExecution[F[_]](input: EventInstance, correlationId: Option[String], currentTime: Long): EventValidation[TransitionExecution] = {
    for {
      transitionAndDescriptor <- eventIsInRecipe(input)
      (transition, descriptor) = transitionAndDescriptor
      _ <- eventIsSound(descriptor, input)
      _ <- withinReceivePeriod(currentTime)
      _ <- notReceivedCorrelationId(correlationId)
      _ <- transitionNotBlocked(transition)
      params <- consumableTokensAreAvailable(transition)
      execution = TransitionExecution(
        recipeInstanceId = recipeInstance.recipeInstanceId,
        recipe = recipeInstance.recipe,
        transition = transition,
        consume = params.head,
        input = Some(input),
        ingredients = recipeInstance.ingredients,
        correlationId = correlationId
      )
    } yield execution
  }

  private def reject[A](rejection: FireSensoryEventRejection, explanation: String): EventValidation[A] =
    Left(rejection -> explanation)

  private def accept[A](a: A): EventValidation[A] =
    Right(a)

  private def continue: EventValidation[Unit] =
    accept(())

  private def eventIsInRecipe(event: EventInstance): EventValidation[(Transition, EventDescriptor)] = {
    val maybeTransition = recipe.petriNet.transitions.find(_.label == event.name)
    val maybeSensoryEvent = recipe.sensoryEvents.find(_.name == event.name)
    (maybeTransition, maybeSensoryEvent) match {
      case (Some(transition), Some(sensoryEvent)) =>
        accept(transition -> sensoryEvent)
      case _ =>
        val msg = s"No event with name '${event.name}' found in recipe '${recipeInstance.recipe.name}'"
        reject(FireSensoryEventRejection.InvalidEvent(recipeInstance.recipeInstanceId, msg), msg)
    }
  }

  private def eventIsSound(descriptor: EventDescriptor, event: EventInstance): EventValidation[Unit] = {
    val eventValidationErrors = event.validate(descriptor)
    if (eventValidationErrors.nonEmpty) {
      val msg = s"Invalid event: " + eventValidationErrors.mkString(",")
      reject(FireSensoryEventRejection.InvalidEvent(recipeInstance.recipeInstanceId, msg), msg)
    } else
      continue
  }

  private def withinReceivePeriod(currentTime: Long): EventValidation[Unit] =
    recipeInstance.recipe.eventReceivePeriod match {
      case Some(receivePeriod) if currentTime - createdOn > receivePeriod.toMillis =>
        reject(FireSensoryEventRejection.ReceivePeriodExpired(recipeInstance.recipeInstanceId), "Receive period expired")
      case _ =>
        continue
    }

  private def notReceivedCorrelationId(correlationId: Option[String]): EventValidation[Unit] = {
    def alreadyReceived(correlation: String): Boolean =
      recipeInstance.completedCorrelationIds.contains(correlation) ||
        recipeInstance.executions.values.exists(_.correlationId.contains(correlation))
    correlationId match {
      case Some(correlationId) if alreadyReceived(correlationId) =>
        reject(FireSensoryEventRejection.AlreadyReceived(recipeInstance.recipeInstanceId, correlationId),
        s"The correlation id $correlationId was previously received by another fire transition command")
      case _ =>
        continue
    }
  }

  private def transitionNotBlocked(transition: Transition): EventValidation[Unit] =
    if (hasFailed(transition))
      reject(FireSensoryEventRejection.FiringLimitMet(recipeInstance.recipeInstanceId),
        "Transition is blocked by a previous failure")
    else
      continue

  private def consumableTokensAreAvailable(transition: Transition): EventValidation[Iterable[Marking[Place]]] = {
    val enabledParams = enabledParameters(availableMarkings)
    enabledParams.get(transition) match {
      case None =>
        reject(FireSensoryEventRejection.FiringLimitMet(recipeInstance.recipeInstanceId),
          s"Not enough consumable tokens. This might have been caused because the event has already been fired up to the firing limit but the recipe requires more instances of the event, use withSensoryEventNoFiringLimit or increase the amount of firing limit on the recipe if such behaviour is desired")
      case Some(params) =>
        accept(params)
    }
  }
}
