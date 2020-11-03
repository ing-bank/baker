package com.ing.baker.runtime.model

import cats.effect.concurrent.Deferred
import cats.effect.{ConcurrentEffect, Timer}
import cats.implicits._
import cats.effect.implicits._
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.il.{CompiledRecipe, RecipeVisualStyle}
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.model.recipeinstance.{EventsLobby, RecipeInstance}
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.types.Value
import com.typesafe.scalalogging.LazyLogging

abstract class Baker[F[_]](implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]) extends BakerF[F] with LazyLogging {

  val timeouts: TimeoutsConfig

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  override def addRecipe(compiledRecipe: CompiledRecipe): F[String] =
    components.recipeManager.addRecipe(compiledRecipe).timeout(timeouts.addRecipeTimeout)

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  override def getRecipe(recipeId: String): F[RecipeInformation] =
    components.recipeManager.getRecipe(recipeId).flatMap[RecipeInformation] {
      case Some((compiledRecipe, timestamp)) =>
        getImplementationErrors(compiledRecipe).map(
          RecipeInformation(compiledRecipe, timestamp, _))
      case None =>
        effect.raiseError(BakerException.NoSuchRecipeException(recipeId))
    }.timeout(timeouts.inquireTimeout)

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes: F[Map[String, RecipeInformation]] =
    components.recipeManager.getAllRecipes.flatMap[Map[String, RecipeInformation]](_.toList
      .traverse { case (recipeId, (compiledRecipe, timestamp)) =>
        getImplementationErrors(compiledRecipe)
          .map(errors => recipeId -> RecipeInformation(compiledRecipe, timestamp, errors))
      }
      .map(_.toMap)
    ).timeout(timeouts.inquireTimeout)

  private def getImplementationErrors(compiledRecipe: CompiledRecipe): F[Set[String]] = {
    //TODO optimize so that we do not have to much traffic if its a remote InteractionManager
    compiledRecipe.interactionTransitions.toList
      .traverse(x => components
        .interactionInstanceManager.contains(x)
        .map(has => (has, x.originalInteractionName)))
      .map(_
        .filterNot(_._1)
        .map(x => s"No implementation provided for interaction: ${x._2}")
        .toSet)
  }

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    *
    * @param recipeId         The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @return
    */
  override def bake(recipeId: String, recipeInstanceId: String): F[Unit] =
    (for {
      recipeInfo <- getRecipe(recipeId)
      outcome <- components.recipeInstanceManager.bake(recipeInstanceId, recipeInfo.compiledRecipe)
      _ <- outcome match {
        case RecipeInstanceManager.BakeOutcome.Baked =>
          effect.unit
        case RecipeInstanceManager.BakeOutcome.RecipeInstanceDeleted =>
          effect.raiseError(BakerException.ProcessDeletedException(recipeInstanceId))
        case RecipeInstanceManager.BakeOutcome.RecipeInstanceAlreadyExists =>
          effect.raiseError(BakerException.ProcessAlreadyExistsException(recipeInstanceId))
      }
    } yield ()).timeout(timeouts.bakeTimeout)

  /**
    * Notifies Baker that an event has happened and waits until the event was accepted but not executed by the process.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event            The event object
    * @param correlationId    Id used to ensure the process instance handles unique events
    */
  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): F[SensoryEventStatus] =
    components.recipeInstanceManager
      .fireEvent(recipeInstanceId, event, correlationId)
      .value.flatMap(mapRejectionsToStatus)
      .timeout(timeouts.processEventTimeout)

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event            The event object
    * @param correlationId    Id used to ensure the process instance handles unique events
    */
  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): F[SensoryEventResult] =
    components.recipeInstanceManager
      .fireEvent(recipeInstanceId, event, correlationId)
      .value.flatMap(mapRejectionsToResult(event.name))
      .timeout(timeouts.processEventTimeout)

  /**
    * Notifies Baker that an event has happened and waits until an specific event has executed.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event            The event object
    * @param onEvent          The name of the event to wait for
    * @param correlationId    Id used to ensure the process instance handles unique events
    */
  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String]): F[SensoryEventResult] =
    components.recipeInstanceManager
      .fireEvent(recipeInstanceId, event, correlationId)
      .value.flatMap(mapRejectionsToResult(onEvent))
      .timeout(timeouts.processEventTimeout)

  /**
    * Notifies Baker that an event has happened and provides 2 async handlers, one for when the event was accepted by
    * the process, and another for when the event was fully executed by the process.
    *
    * Possible failures:
    * `NoSuchProcessException` -> When no process exists for the given id
    * `ProcessDeletedException` -> If the process is already deleted
    *
    * @param recipeInstanceId The process identifier
    * @param event            The event object
    * @param correlationId    Id used to ensure the process instance handles unique events
    */
  override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): EventResolutionsF[F] = {
    val fireDeferred = Deferred.unsafe[F, Either[FireSensoryEventRejection, EventsLobby[F]]]
    val runProgram = components.recipeInstanceManager.fireEvent(recipeInstanceId, event, correlationId)
    effect.runAsync(runProgram.value) {
      case Right(outcome) => effect.toIO(fireDeferred.complete(outcome))
      case Left(e) => RecipeInstance.logImpossibleException(logger, e)
    }
    new EventResolutionsF[F] {
      override def resolveWhenReceived: F[SensoryEventStatus] =
        fireDeferred.get.flatMap(mapRejectionsToStatus)
          .timeout(timeouts.processEventTimeout)

      override def resolveWhenCompleted: F[SensoryEventResult] =
        fireDeferred.get.flatMap(mapRejectionsToResult(event.name))
          .timeout(timeouts.processEventTimeout)
    }
  }

  private def mapRejectionsToStatus(outcome: Either[FireSensoryEventRejection, EventsLobby[F]]): F[SensoryEventStatus] =
    outcome match {
      case Left(FireSensoryEventRejection.InvalidEvent(_, message)) =>
        effect.raiseError(BakerException.IllegalEventException(message))
      case Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0)) =>
        effect.raiseError(BakerException.NoSuchProcessException(recipeInstanceId0))
      case Left(_: FireSensoryEventRejection.FiringLimitMet) =>
        effect.pure(SensoryEventStatus.FiringLimitMet)
      case Left(_: FireSensoryEventRejection.AlreadyReceived) =>
        effect.pure(SensoryEventStatus.AlreadyReceived)
      case Left(_: FireSensoryEventRejection.ReceivePeriodExpired) =>
        effect.pure(SensoryEventStatus.ReceivePeriodExpired)
      case Left(_: FireSensoryEventRejection.RecipeInstanceDeleted) =>
        effect.pure(SensoryEventStatus.RecipeInstanceDeleted)
      case Right(_) =>
        effect.pure(SensoryEventStatus.Received)
    }

  private def mapRejectionsToResult(eventToAwaitFor: String)(outcome: Either[FireSensoryEventRejection, EventsLobby[F]]): F[SensoryEventResult] =
    outcome match {
      case Left(FireSensoryEventRejection.InvalidEvent(_, message)) =>
        effect.raiseError(BakerException.IllegalEventException(message))
      case Left(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0)) =>
        effect.raiseError(BakerException.NoSuchProcessException(recipeInstanceId0))
      case Left(_: FireSensoryEventRejection.FiringLimitMet) =>
        effect.pure(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.AlreadyReceived) =>
        effect.pure(SensoryEventResult(SensoryEventStatus.AlreadyReceived, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.ReceivePeriodExpired) =>
        effect.pure(SensoryEventResult(SensoryEventStatus.ReceivePeriodExpired, Seq.empty, Map.empty))
      case Left(_: FireSensoryEventRejection.RecipeInstanceDeleted) =>
        effect.pure(SensoryEventResult(SensoryEventStatus.RecipeInstanceDeleted, Seq.empty, Map.empty))
      case Right(lobby) =>
        lobby.awaitForEvent(eventToAwaitFor)
    }

  /**
    * Returns an index of all running processes.
    *
    * Can potentially return a partial index when baker runs in cluster mode
    * and not all shards can be reached within the given timeout.
    *
    * Does not include deleted processes.
    *
    * @return An index of all processes
    */
  override def getAllRecipeInstancesMetadata: F[Set[RecipeInstanceMetadata]] =
    components.recipeInstanceManager.getAllRecipeInstancesMetadata
      .timeout(timeouts.inquireTimeout)

  /**
    * Returns the process state.
    *
    * @param recipeInstanceId The process identifier
    * @return The process state.
    */
  override def getRecipeInstanceState(recipeInstanceId: String): F[RecipeInstanceState] =
    components.recipeInstanceManager.getRecipeInstanceState(recipeInstanceId).flatMap[RecipeInstanceState] {
      case RecipeInstanceManager.GetRecipeInstanceStateOutcome.Success(state) =>
        effect.pure(state)
      case RecipeInstanceManager.GetRecipeInstanceStateOutcome.NoSuchRecipeInstance =>
        effect.raiseError(BakerException.NoSuchProcessException(recipeInstanceId))
      case RecipeInstanceManager.GetRecipeInstanceStateOutcome.RecipeInstanceDeleted =>
        effect.raiseError(BakerException.ProcessDeletedException(recipeInstanceId))
    }.timeout(timeouts.inquireTimeout)

  /**
    * Returns all provided ingredients for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The provided ingredients.
    */
  override def getIngredients(recipeInstanceId: String): F[Map[String, Value]] =
    getRecipeInstanceState(recipeInstanceId).map(_.ingredients)

  /**
    * Returns all fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The events
    */
  override def getEvents(recipeInstanceId: String): F[Seq[EventMoment]] =
    getRecipeInstanceState(recipeInstanceId).map(_.events)

  /**
    * Returns all names of fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The event names
    */
  override def getEventNames(recipeInstanceId: String): F[Seq[String]] =
    getRecipeInstanceState(recipeInstanceId).map(_.eventNames)

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param recipeInstanceId The process identifier.
    * @return A visual (.dot) representation of the process state.
    */
  override def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle): F[String] = ???

  private def doRegisterEventListener(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit, processFilter: String => Boolean): F[Unit] =
    registerBakerEventListener {
      case EventReceived(_, recipeName, recipeId, recipeInstanceId, _, event) if processFilter(recipeName) =>
        listenerFunction.apply(RecipeEventMetadata(recipeId = recipeId, recipeName = recipeName, recipeInstanceId = recipeInstanceId), event)
      case InteractionCompleted(_, _, recipeName, recipeId, recipeInstanceId, _, Some(event)) if processFilter(recipeName) =>
        listenerFunction.apply(RecipeEventMetadata(recipeId = recipeId, recipeName = recipeName, recipeInstanceId = recipeInstanceId), event)
      case InteractionFailed(_, _, recipeName, recipeId, recipeInstanceId, _, _, _, ExceptionStrategyOutcome.Continue(eventName)) if processFilter(recipeName) =>
        listenerFunction.apply(RecipeEventMetadata(recipeId = recipeId, recipeName = recipeName, recipeInstanceId = recipeInstanceId), EventInstance(eventName, Map.empty))
      case _ => ()
    }

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(recipeName: String, listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): F[Unit] =
    doRegisterEventListener(listenerFunction, _ == recipeName)

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): F[Unit] =
    doRegisterEventListener(listenerFunction, _ => true)

  /**
    * Registers a listener function that listens to all BakerEvents
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    *
    * @param listenerFunction
    * @return
    */
  override def registerBakerEventListener(listenerFunction: BakerEvent => Unit): F[Unit] =
    components.eventStream.subscribe(listenerFunction)
      .timeout(timeouts.inquireTimeout)

  /**
    * Adds an interaction implementation to baker.
    *
    * @param implementation The implementation object
    */
  override def addInteractionInstance(implementation: InteractionInstanceF[F]): F[Unit] =
    components.interactionInstanceManager.add(implementation)
      .timeout(timeouts.addRecipeTimeout)

  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  override def addInteractionInstances(implementations: Seq[InteractionInstanceF[F]]): F[Unit] =
    implementations.toList.traverse(components.interactionInstanceManager.add).void
      .timeout(timeouts.addRecipeTimeout)

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  override def retryInteraction(recipeInstanceId: String, interactionName: String): F[Unit] = ???

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): F[Unit] = ???

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): F[Unit] = ???
}
