package com.ing.baker.runtime.model

import cats.effect.{ConcurrentEffect, ContextShift, IO, Timer}
import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.BakerException.{IllegalEventException, NoSuchProcessException, NoSuchRecipeException, ProcessAlreadyExistsException}
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common.{RejectReason, SensoryEventStatus}
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.scaladsl._

trait RecipeManager[F[_]] {

  def addRecipe(compiledRecipe: CompiledRecipe): F[String]

  def getRecipe(recipeId: String): F[Either[NoSuchRecipeException, RecipeInformation]]

  def getAllRecipes: F[Map[String, RecipeInformation]]
}


abstract class InteractionManager[F[_]](implicit eff: ConcurrentEffect[F], contextShift: ContextShift[IO]) {

  def addImplementation(interaction: InteractionInstance): F[Unit]

  def getImplementation(interaction: InteractionTransition): F[Option[InteractionInstance]]

  def hasImplementation(interaction: InteractionTransition): F[Boolean] =
    getImplementation(interaction).map(_.isDefined)

  def executeImplementation(interaction: InteractionTransition, input: Seq[IngredientInstance]): F[Option[EventInstance]] = {
    getImplementation(interaction).flatMap {
      case Some(implementation) => eff.liftIO(IO.fromFuture(IO(implementation.run(input))))
      case None => eff.raiseError(new IllegalStateException(s"No implementation available for interaction ${interaction.interactionName}"))
    }
  }

  protected def isCompatibleImplementation(interaction: InteractionTransition, implementation: InteractionInstance): Boolean = {
    val interactionNameMatches =
      interaction.originalInteractionName == implementation.name
    val inputSizeMatches =
      implementation.input.size == interaction.requiredIngredients.size
    val inputNamesAndTypesMatches =
      interaction
        .requiredIngredients
        .forall { descriptor =>
          implementation.input.exists(_.isAssignableFrom(descriptor.`type`))
        }
    interactionNameMatches && inputSizeMatches && inputNamesAndTypesMatches
  }
}

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

/* This is going great, except `EventResolutions` and `Interactioninstance` should be parametriced on the effect type F[_], now are set to Future, this has some implications

abstract class Baker[F[_]](recipeManager: RecipeManager[F],
                           interactionManager: InteractionManager[F],
                           recipeInstanceManager: RecipeInstanceManager[F])
                          (implicit timer: Timer[F], eff: ConcurrentEffect[F]) extends common.Baker[F] with ScalaApi {

  override type SensoryEventResultType = SensoryEventResult

  override type EventResolutionsType = EventResolutions

  override type EventInstanceType = EventInstance

  override type RecipeInstanceStateType = RecipeInstanceState

  override type InteractionInstanceType = InteractionInstance

  override type BakerEventType = BakerEvent

  override type RecipeInstanceMetadataType = RecipeInstanceMetadata

  override type RecipeInformationType = RecipeInformation

  override type EventMomentType = EventMoment

  override type RecipeMetadataType = RecipeEventMetadata

  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance): F[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, None)

  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance): F[SensoryEventResultType] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, None)

  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String): F[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, None)

  override def fireEvent(recipeInstanceId: String, event: EventInstance): EventResolutionsType =
    fireEvent(recipeInstanceId, event, None)

  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: String): F[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, Some(correlationId))

  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: String): F[SensoryEventResultType] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, Some(correlationId))

  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: String): F[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Some(correlationId))

  override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: String): EventResolutionsType =
    fireEvent(recipeInstanceId, event, Some(correlationId))

  override def addRecipe(compiledRecipe: CompiledRecipe): F[String] =
    recipeManager.addRecipe(compiledRecipe)

  override def getRecipe(recipeId: String): F[RecipeInformation] =
    recipeManager.getRecipe(recipeId).flatMap {
      case Right(a) => eff.pure(a)
      case Left(e) => eff.raiseError(e)
    }

  override def getAllRecipes: F[Map[String, RecipeInformation]] =
    recipeManager.getAllRecipes

  override def addInteractionInstance(implementation: InteractionInstance): F[Unit] =
    interactionManager.addImplementation(implementation)

  override def bake(recipeId: String, recipeInstanceId: String): F[Unit] =
    recipeInstanceManager.bake(recipeId, recipeInstanceId).flatMap {
      case RecipeInstanceManager.BakeOutcome.Baked =>
        eff.unit
      case RecipeInstanceManager.BakeOutcome.RecipeInstanceDeleted =>
        eff.raiseError(ProcessAlreadyExistsException(recipeInstanceId))
      case RecipeInstanceManager.BakeOutcome.RecipeInstanceAlreadyExists =>
        eff.raiseError(NoSuchRecipeException(recipeId))
    }

  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): F[SensoryEventStatus] =
    recipeInstanceManager.fireEventAndResoleWhenReceived(recipeInstanceId, event, correlationId).flatMap {
      case Left(FireSensoryEventRejection.InvalidEvent(_, message)) =>
        eff.raiseError(IllegalEventException(message))
      case Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0)) =>
        eff.raiseError(NoSuchProcessException(recipeInstanceId0))
      case Left(_: FireSensoryEventRejection.FiringLimitMet) =>
        eff.pure(SensoryEventStatus.FiringLimitMet)
      case Left(_: FireSensoryEventRejection.AlreadyReceived) =>
        eff.pure(SensoryEventStatus.AlreadyReceived)
      case Left(_: FireSensoryEventRejection.ReceivePeriodExpired) =>
        eff.pure(SensoryEventStatus.ReceivePeriodExpired)
      case Left(_: FireSensoryEventRejection.RecipeInstanceDeleted) =>
        eff.pure(SensoryEventStatus.RecipeInstanceDeleted)
      case Right(status) =>
        eff.pure(status)
    }

  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): F[SensoryEventResult] =
    recipeInstanceManager.fireEventAndResoleWhenCompleted(recipeInstanceId, event, correlationId, waitForRetries = true).flatMap {
      case Left(FireSensoryEventRejection.InvalidEvent(_, message)) =>
        eff.raiseError(IllegalEventException(message))
      case Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0)) =>
        eff.raiseError(NoSuchProcessException(recipeInstanceId0))
      case Left(_: FireSensoryEventRejection.FiringLimitMet) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.AlreadyReceived) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.AlreadyReceived, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.ReceivePeriodExpired) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.ReceivePeriodExpired, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.RecipeInstanceDeleted) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.RecipeInstanceDeleted, Seq.empty, Map.empty))
      case Right(result) =>
        eff.pure(result)
    }

  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstanceType, onEvent: String, correlationId: Option[String]): F[SensoryEventResult] =
    recipeInstanceManager.fireEventAndResolveOnEvent(recipeInstanceId, event, correlationId, waitForRetries = true, onEvent).flatMap {
      case Left(FireSensoryEventRejection.InvalidEvent(_, message)) =>
        eff.raiseError(IllegalEventException(message))
      case Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0)) =>
        eff.raiseError(NoSuchProcessException(recipeInstanceId0))
      case Left(_: FireSensoryEventRejection.FiringLimitMet) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.AlreadyReceived) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.AlreadyReceived, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.ReceivePeriodExpired) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.ReceivePeriodExpired, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.RecipeInstanceDeleted) =>
        eff.pure(SensoryEventResult(SensoryEventStatus.RecipeInstanceDeleted, Seq.empty, Map.empty))
      case Right(result) =>
        eff.pure(result)
    }

  override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): EventResolutions = ???



  /*
  processIndexActor.ask(ProcessEvent(
    recipeInstanceId = recipeInstanceId,
    event = event,
    correlationId = correlationId,
    timeout = config.timeouts.defaultProcessEventTimeout,
    reaction = FireSensoryEventReaction.NotifyWhenCompleted(waitForRetries = true)
  ))(config.timeouts.defaultProcessEventTimeout).flatMap {
    case FireSensoryEventRejection.InvalidEvent(_, message) =>
      F.failed(IllegalEventException(message))
    case FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0) =>
      F.raiseError(NoSuchProcessException(recipeInstanceId0))
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
 */
