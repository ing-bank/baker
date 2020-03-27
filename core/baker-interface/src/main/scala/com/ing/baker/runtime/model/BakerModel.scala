package com.ing.baker.runtime.model

import cats.data.State
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet.Transition
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.runtime.common.BakerException.{IllegalEventException, NoSuchProcessException, NoSuchRecipeException, ProcessAlreadyExistsException}
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.model.AsyncModel.AsyncModelTypeSetter
import com.ing.baker.runtime.model.BakerModel._
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstance, RecipeInformation, SensoryEventResult}
import com.ing.baker.petrinet.api._

object BakerModel extends AsyncModelTypeSetter[BakerModelState, BakerException] {

  type Model[+A] = AsyncModel[BakerModelState, BakerException, A]
}

class BakerModel extends Baker[Model] {

  override def addRecipe(compiledRecipe: CompiledRecipe): Model[String] =
    for {
      timestamp <- currentTime
      _ <- asyncUpdate(_.addRecipe(compiledRecipe, timestamp))
    } yield compiledRecipe.recipeId

  override def getRecipe(recipeId: String): Model[RecipeInformation] =
    for {
      state <- asyncInspect
      recipeInformation <- state.recipes.get(recipeId) match {
        case None => fail(NoSuchRecipeException(recipeId))
        case Some((timestamp, recipe)) => ok(RecipeInformation(recipe, timestamp, Set.empty)) // Implementation errors are going to be removed
      }
    } yield recipeInformation

  override def getAllRecipes: Model[Map[String, RecipeInformation]] =
    ???

  override def addInteractionInstance(implementation: InteractionInstance): Model[Unit] =
    ???

  override def bake(recipeId: String, recipeInstanceId: String): Model[Unit] =
    for {
      state <- asyncInspect
      maybeRecipe = state.recipes.get(recipeId)
      maybeRecipeInstance = state.recipeInstances.get(recipeInstanceId)
      _ <- (maybeRecipe, maybeRecipeInstance) match {
        case (Some((_, recipe)), None) =>
          set(state.bake(recipe, recipeInstanceId))
        case (_, Some(_)) =>
          fail(ProcessAlreadyExistsException(recipeInstanceId))
        case (None, _) =>
          fail(NoSuchRecipeException(recipeId))
      }
    } yield ()

  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance): Model[SensoryEventResult] =
    for {
      state <- asyncInspect
      recipeInstanceState <- validate {
        state.recipeInstances.get(recipeInstanceId)
          .toRight(NoSuchProcessException(recipeInstanceId))
      }
      transition <- validate {
        recipeInstanceState.recipe.petriNet.transitions.find(_.label == event.name)
          .toRight(IllegalEventException(s"No event with name '${event.name}' found in recipe '${recipeInstanceState.recipe.name}'"))
      }
      sensoryEventDescriptor <- validate {
        recipeInstanceState.recipe.sensoryEvents.find(_.name == event.name)
          .toRight(IllegalEventException(s"No event with name '${event.name}' found in recipe '${recipeInstanceState.recipe.name}'"))
      }
      _ <- validate {
        val errors = event.validate(sensoryEventDescriptor)
        if (errors.nonEmpty) Left(IllegalEventException(s"Invalid event: " + errors.mkString(",")))
        else Right(())
      }
      sensoryEventResult <- {
        if (recipeInstanceState.isBlocked(transition))
          ok(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
        else
          recipeInstanceState.createFiring(transition, event) match {
            case Left(_) =>
              ok(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
            case Right((nextRecipeInstanceState, transitionFiring)) =>
              ???
          }
      }
    } yield sensoryEventResult

  private def executeTransition(transitionFiring: TransitionFiring): Model[TransitionEvent] =
    for {
      startTime <- asyncStep
      consumed: Marking[Long] = transitionFiring.consume.marshall
    } yield transitionEvent

    ???
    /*
    IO.unit.flatMap { _ =>
      // calling transitionTask(...) could potentially throw an exception
      // TODO I don't believe the last statement is true
      transitionTask(topology, transition)(job.consume, job.processState, job.input)
    }.map {
      case (producedMarking, out) ⇒
        TransitionFiredEvent(job.id, transition.getId, job.correlationId, startTime, System.currentTimeMillis(), consumed, producedMarking.marshall, out)
    }.handleException {
      // In case an exception was thrown by the transition, we compute the failure strategy and return a TransitionFailedEvent
      case e: Throwable ⇒
        val failureCount = job.failureCount + 1
        val failureStrategy = handleException(job)(e, failureCount, startTime, topology.outMarking(transition))
        TransitionFailedEvent(job.id, transition.getId, job.correlationId, startTime, System.currentTimeMillis(), consumed, job.input, exceptionStackTrace(e), failureStrategy)
    }.handleException {
      // If an exception was thrown while computing the failure strategy we block the interaction from firing
      case e: Throwable =>
        logger.error(s"Exception while handling transition failure", e)
        TransitionFailedEvent(job.id, transition.getId, job.correlationId, startTime, System.currentTimeMillis(), consumed, job.input, exceptionStackTrace(e), FailureStrategy.BlockTransition)
    }
     */

  /*
  processIndexActor.ask(ProcessEvent(
    recipeInstanceId = recipeInstanceId,
    event = event,
    correlationId = correlationId,
    timeout = config.timeouts.defaultProcessEventTimeout,
    reaction = FireSensoryEventReaction.NotifyWhenCompleted(waitForRetries = true)
  ))(config.timeouts.defaultProcessEventTimeout).flatMap {
    case FireSensoryEventRejection.InvalidEvent(_, message) =>
      Future.failed(IllegalEventException(message))
    case FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0) =>
      Future.failed(NoSuchProcessException(recipeInstanceId0))
    case _: FireSensoryEventRejection.FiringLimitMet =>
      Future.successful(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
    case _: FireSensoryEventRejection.AlreadyReceived =>
      Future.successful(SensoryEventResult(SensoryEventStatus.AlreadyReceived, Seq.empty, Map.empty))
    case _: FireSensoryEventRejection.ReceivePeriodExpired =>
      Future.successful(SensoryEventResult(SensoryEventStatus.ReceivePeriodExpired, Seq.empty, Map.empty))
    case _: FireSensoryEventRejection.RecipeInstanceDeleted =>
      Future.successful(SensoryEventResult(SensoryEventStatus.RecipeInstanceDeleted, Seq.empty, Map.empty))
    case ProcessEventCompletedResponse(result) =>
      Future.successful(result)
  }
   */

}