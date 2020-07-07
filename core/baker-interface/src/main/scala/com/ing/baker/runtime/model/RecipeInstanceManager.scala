package com.ing.baker.runtime.model

import cats.effect.ConcurrentEffect
import com.ing.baker.runtime.common.{RejectReason, SensoryEventStatus}
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.scaladsl.{EventInstance, SensoryEventResult}

object RecipeInstanceManager {

  sealed trait BakeOutcome

  object BakeOutcome {

    case object Baked extends BakeOutcome

    case object RecipeInstanceDeleted extends BakeOutcome

    case object RecipeInstanceAlreadyExists extends BakeOutcome
  }

  sealed trait FireSensoryEventRejection {

    def asReason: RejectReason
  }

  object FireSensoryEventRejection {

    /**
      * Indicates that a process can no longer receive events because the configured period has expired.
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class ReceivePeriodExpired(recipeInstanceId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.ReceivePeriodExpired
    }

    /**
      * @param msg error message for the request
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class InvalidEvent(recipeInstanceId: String, msg: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.InvalidEvent
    }

    /**
      * Returned if a process has been deleted
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class RecipeInstanceDeleted(recipeInstanceId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.ProcessDeleted
    }

    /**
      * Returned if the process is uninitialized
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class NoSuchRecipeInstance(recipeInstanceId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.NoSuchProcess
    }

    /**
      * The firing limit, the number of times this event may fire, was met.
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      */
    case class FiringLimitMet(recipeInstanceId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.FiringLimitMet
    }

    /**
      * An event with the same correlation id was already received.
      *
      * @param recipeInstanceId The identifier of the RecipeInstanceId
      * @param correlationId The identifier used to secure uniqueness
      */
    case class AlreadyReceived(recipeInstanceId: String, correlationId: String) extends FireSensoryEventRejection {

      def asReason: RejectReason = RejectReason.AlreadyReceived
    }
  }
}

abstract class RecipeInstanceManager[F[_]](implicit eff: ConcurrentEffect[F]) {

  def bake(recipeId: String, recipeInstanceId: String): F[RecipeInstanceManager.BakeOutcome]

  def fireEventAndResoleWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): F[Either[FireSensoryEventRejection, SensoryEventStatus]]

  def fireEventAndResoleWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String], waitForRetries: Boolean): F[Either[FireSensoryEventRejection, SensoryEventResult]]

  def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String], waitForRetries: Boolean, onEvent: String): F[Either[FireSensoryEventRejection, SensoryEventResult]]

  /*
  type FireEventValidation[A] = EitherT[F, FireSensoryEventRejection, A]

  def reject[A](rejection: FireSensoryEventRejection): FireEventValidation[A] =
    EitherT.leftT(rejection)

  def accept[A](a: A): FireEventValidation[A] =
    EitherT.rightT(a)

  def continue: FireEventValidation[Unit] =
    accept(())

  def validateEventIsInRecipe(event: EventInstance, recipeInstanceId: String, recipe: CompiledRecipe): FireEventValidation[(Transition, EventDescriptor)] = {
    val transition0 = recipe.petriNet.transitions.find(_.label == event.name)
    val sensoryEvent0 = recipe.sensoryEvents.find(_.name == event.name)
    (transition0, sensoryEvent0) match {
      case (Some(transition), Some(sensoryEvent)) =>
        accept(transition -> sensoryEvent)
      case _ =>
        reject(FireSensoryEventRejection.InvalidEvent(
          recipeInstanceId,
          s"No event with name '${event.name}' found in recipe '${recipe.name}'"
        ))
    }
  }

  def validateEventIsSound(event: EventInstance, descriptor: EventDescriptor): FireEventValidation[Unit] = {
    val eventValidationErrors = event.validate(descriptor)
    if (eventValidationErrors.nonEmpty)
      reject(FireSensoryEventRejection.InvalidEvent(
        recipeInstanceId,
        s"Invalid event: " + eventValidationErrors.mkString(",")
      ))
    else continue
  }

  def validateWithinReceivePeriod(recipe: CompiledRecipe, metadata: ActorMetadata): FireEventValidation[Unit] = {
    def outOfReceivePeriod(current: Long, period: FiniteDuration): Boolean =
      current - metadata.createdDateTime > period.toMillis
    for {
      currentTime <- fetchCurrentTime
      _ <- recipe.eventReceivePeriod match {
        case Some(receivePeriod) if outOfReceivePeriod(currentTime, receivePeriod) =>
          reject(FireSensoryEventRejection.ReceivePeriodExpired(recipeInstanceId))
        case _ => continue
      }
    } yield ()
  }
   */

  /*
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
   */

  /*
private def executeTransition(transitionFiring: TransitionFiring): F[TransitionEvent] =
  for {
    startTime <- asyncStep
    consumed: Marking[Long] = transitionFiring.consume.marshall
  } yield ???

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
}

