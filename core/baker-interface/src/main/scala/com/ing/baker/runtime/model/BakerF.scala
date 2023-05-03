package com.ing.baker.runtime.model

import cats.effect.implicits._
import cats.effect.{ConcurrentEffect, Timer}
import cats.implicits._
import cats.~>
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.il.{RecipeVisualStyle, RecipeVisualizer}
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.BakerException.NoSuchIngredientException
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common.{BakerException, InteractionExecutionFailureReason, RecipeRecord, SensoryEventStatus}
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance
import com.ing.baker.runtime.scaladsl.{Baker => DeprecatedBaker, _}
import com.ing.baker.types.Value
import com.typesafe.scalalogging.LazyLogging

import scala.collection.immutable.Seq
import scala.concurrent.Future
import scala.concurrent.duration._

/**
  * TODO create a Resource based runtime execution which runs the retention period stream and allocates a Blocker context
  */
object BakerF {

  case class Config(allowAddingRecipeWithoutRequiringInstances: Boolean = false,
                    recipeInstanceConfig: RecipeInstance.Config = RecipeInstance.Config(),
                    idleTimeout: FiniteDuration = 60 seconds,
                    retentionPeriodCheckInterval: FiniteDuration = 10.seconds,
                    bakeTimeout: FiniteDuration = 10.seconds,
                    processEventTimeout: FiniteDuration = 10.seconds,
                    inquireTimeout: FiniteDuration = 60.seconds,
                    shutdownTimeout: FiniteDuration = 10.seconds,
                    addRecipeTimeout: FiniteDuration = 10.seconds,
                    executeSingleInteractionTimeout: FiniteDuration = 60.seconds,
                   )
}

abstract class BakerF[F[_]](implicit components: BakerComponents[F], effect: ConcurrentEffect[F], timer: Timer[F]) extends common.Baker[F] with ScalaApi with LazyLogging {
  self =>

  val config: BakerF.Config

  override type SensoryEventResultType = SensoryEventResult

  override type EventResolutionsType = EventResolutionsF[F]

  override type EventInstanceType = EventInstance

  override type InteractionInstanceType = com.ing.baker.runtime.model.InteractionInstance[F]

  override type RecipeInstanceStateType = RecipeInstanceState

  override type InteractionInstanceDescriptorType = InteractionInstanceDescriptor

  override type IngredientInstanceType = IngredientInstance

  override type BakerEventType = BakerEvent

  override type RecipeInstanceMetadataType = RecipeInstanceMetadata

  override type RecipeInformationType = RecipeInformation

  override type EventMomentType = EventMoment

  override type RecipeMetadataType = RecipeEventMetadata

  override type InteractionExecutionResultType = InteractionExecutionResult

  private def javaTimeoutToBakerTimeout[A](operationName: String) : PartialFunction[Throwable, F[A]] = {
    case _ : java.util.concurrent.TimeoutException => effect.raiseError(BakerException.TimeoutException(operationName))
  }

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param recipeRecord The RecipeRecord of the recipe
    * @return A recipeId
    */
  override def addRecipe(recipeRecord: RecipeRecord): F[String] =
    components
      .recipeManager
      .addRecipe(recipeRecord.recipe, !recipeRecord.validate || config.allowAddingRecipeWithoutRequiringInstances)
      .timeout(config.addRecipeTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("addRecipe"))

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  override def getRecipe(recipeId: String): F[RecipeInformation] =
    components.recipeManager.getRecipe(recipeId)
      .timeout(config.inquireTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("getRecipe"))


  override def getRecipeVisual(recipeId: String, style: RecipeVisualStyle): F[String] =
    components.recipeManager.getRecipe(recipeId).map(recipe =>
      RecipeVisualizer.visualizeRecipe(recipe.compiledRecipe, style))

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes: F[Map[String, RecipeInformation]] =
    components.recipeManager.getAllRecipes
      .timeout(config.inquireTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("getAllRecipes"))


  override def getInteraction(interactionName: String): F[Option[InteractionInstanceDescriptor]] =
    components.interactions
      .listAll
      .map(_.find(_.name == interactionName)
        .map(i => InteractionInstanceDescriptor(i.shaBase64, i.name, i.input, i.output)))


  override def getAllInteractions: F[Seq[InteractionInstanceDescriptor]] =
    components.interactions.listAll
      .map(_.map(i => InteractionInstanceDescriptor(i.shaBase64, i.name, i.input, i.output)))

  override def executeSingleInteraction(interactionId: String, ingredients: Seq[IngredientInstance]): F[InteractionExecutionResult] =
    components.interactions
      .listAll
      .map(interactionsList => interactionsList.find(_.shaBase64 == interactionId))
      .flatMap {
        case None => effect.pure(InteractionExecutionResult(Left(InteractionExecutionResult.Failure(
          InteractionExecutionFailureReason.INTERACTION_NOT_FOUND, None, None))))
        case Some(interactionInstance) =>
          interactionInstance.execute(ingredients, Map.empty)
            .map(executionSuccess => InteractionExecutionResult(Right(InteractionExecutionResult.Success(executionSuccess))))
            .recover {
              case e => InteractionExecutionResult(Left(InteractionExecutionResult.Failure(
                InteractionExecutionFailureReason.INTERACTION_EXECUTION_ERROR,
                Some(interactionInstance.name),
                Some(s"Interaction execution failed. Interaction threw ${e.getClass.getSimpleName} with message ${e.getMessage}."))))
            }
            .timeoutTo(config.executeSingleInteractionTimeout, effect.pure(InteractionExecutionResult(Left(InteractionExecutionResult.Failure(
              InteractionExecutionFailureReason.TIMEOUT, Some(interactionInstance.name), None)))))
            .recoverWith(javaTimeoutToBakerTimeout("executeSingleInteraction"))
      }


  /**
   * Attempts to gracefully shutdown the baker system.
   */
  override def gracefulShutdown(): F[Unit] = ???

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    *
    * @param recipeId         The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @return
    */
  override def bake(recipeId: String, recipeInstanceId: String): F[Unit] =
    components.recipeInstanceManager.bake(recipeId, recipeInstanceId, config.recipeInstanceConfig)
      .timeout(config.bakeTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("bake"))

  /**
    *
    * @param recipeId         The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @param metadata
    *  @return
    */
  override def bake(recipeId: String, recipeInstanceId: String, metadata: Map[String, String]): F[Unit] =
    components.recipeInstanceManager.bake(recipeId, recipeInstanceId, config.recipeInstanceConfig)
      .timeout(config.bakeTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("bake"))
      .flatMap(_ => components.recipeInstanceManager.addMetaData(recipeInstanceId, metadata))

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
      .fireEventAndResolveWhenReceived(recipeInstanceId, event, correlationId)
      .timeout(config.processEventTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("fireEventAndResolveWhenReceived"))

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
      .fireEventAndResolveWhenCompleted(recipeInstanceId, event, correlationId)
      .timeout(config.processEventTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("fireEventAndResolveWhenCompleted"))

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
      .fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, correlationId)
      .timeout(config.processEventTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("fireEventAndResolveOnEvent"))

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
    val (onReceive, onComplete) = components.recipeInstanceManager.fireEvent(recipeInstanceId, event, correlationId).toIO.unsafeRunSync()
    new EventResolutionsF[F] {
      override def resolveWhenReceived: F[SensoryEventStatus] =
        onReceive.timeout(config.processEventTimeout).recoverWith(javaTimeoutToBakerTimeout("fireEvent"))
      override def resolveWhenCompleted: F[SensoryEventResult] =
        onComplete.timeout(config.processEventTimeout).recoverWith(javaTimeoutToBakerTimeout("fireEvent"))
    }
  }

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

  override def addMetaData(recipeInstanceId: String, metadata: Map[String, String]): F[Unit] =
    components.recipeInstanceManager.addMetaData(recipeInstanceId, metadata)


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
      .timeout(config.inquireTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("getAllRecipeInstancesMetadata"))

  /**
    * Returns the process state.
    *
    * @param recipeInstanceId The process identifier
    * @return The process state.
    */
  override def getRecipeInstanceState(recipeInstanceId: String): F[RecipeInstanceState] =
    components.recipeInstanceManager.getRecipeInstanceState(recipeInstanceId)
      .timeout(config.inquireTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("getRecipeInstanceState"))

//  /**
//    * Returns all provided ingredients for a given RecipeInstance id.
//    *
//    * @param recipeInstanceId The process id.
//    * @return The provided ingredients.
//    */
//  override def getIngredient(recipeInstanceId: String, name: String): F[Value] = {
//    getRecipeInstanceState(recipeInstanceId).map(_.ingredients)
//      .map(x => x.get(name) match {
//        case Some(value) => value
//        case None => throw NoSuchIngredientException(name)
//      })
//  }

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
  override def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle = RecipeVisualStyle.default): F[String] =
    components.recipeInstanceManager.getVisualState(recipeInstanceId, style)
      .timeout(config.inquireTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("getVisualState"))

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
      .timeout(config.inquireTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("registerBakerEventListener"))

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  override def retryInteraction(recipeInstanceId: String, interactionName: String): F[Unit] =
    components.recipeInstanceManager.retryBlockedInteraction(recipeInstanceId, interactionName)
      .flatMap(_.compile.drain)
      .timeout(config.processEventTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("retryInteraction"))

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): F[Unit] =
    components.recipeInstanceManager.resolveBlockedInteraction(recipeInstanceId, interactionName, event)
      .flatMap(_.compile.drain)
      .timeout(config.processEventTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("resolveInteraction"))

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): F[Unit] =
    components.recipeInstanceManager.stopRetryingInteraction(recipeInstanceId, interactionName)
      .timeout(config.processEventTimeout)
      .recoverWith(javaTimeoutToBakerTimeout("stopRetryingInteraction"))

  def translate[G[_]](mapK: F ~> G, comapK: G ~> F)(implicit components: BakerComponents[G], effect: ConcurrentEffect[G], timer: Timer[G]): BakerF[G] =
    new BakerF[G] {
      override val config: BakerF.Config =
        self.config
      override def addRecipe(recipeRecord: RecipeRecord): G[String] =
        mapK(self.addRecipe(recipeRecord))
      override def getRecipe(recipeId: String): G[RecipeInformation] =
        mapK(self.getRecipe(recipeId))
      override def getRecipeVisual(recipeId: String, style: RecipeVisualStyle): G[String] =
        mapK(self.getRecipeVisual(recipeId))
      override def getAllRecipes: G[Map[String, RecipeInformation]] =
        mapK(self.getAllRecipes)
      override def getAllInteractions: G[Seq[InteractionInstanceDescriptor]] =
        mapK(self.getAllInteractions)
      override def getInteraction(interactionName: String): G[Option[InteractionInstanceDescriptor]] =
        mapK(self.getInteraction(interactionName))
      override def executeSingleInteraction(interactionId: String, ingredients: Seq[IngredientInstance]): G[InteractionExecutionResult] =
        mapK(self.executeSingleInteraction(interactionId, ingredients))
      override def bake(recipeId: String, recipeInstanceId: String): G[Unit] =
        mapK(self.bake(recipeId, recipeInstanceId))
      override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): G[SensoryEventStatus] =
        mapK(self.fireEventAndResolveWhenReceived(recipeInstanceId, event, correlationId))
      override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): G[SensoryEventResult] =
        mapK(self.fireEventAndResolveWhenCompleted(recipeInstanceId, event, correlationId))
      override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String]): G[SensoryEventResult] =
        mapK(self.fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, correlationId))
      override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): EventResolutionsF[G] =
        self.fireEvent(recipeInstanceId, event, correlationId).translate(mapK)
      override def getAllRecipeInstancesMetadata: G[Set[RecipeInstanceMetadata]] =
        mapK(self.getAllRecipeInstancesMetadata)
      override def getRecipeInstanceState(recipeInstanceId: String): G[RecipeInstanceState] =
        mapK(self.getRecipeInstanceState(recipeInstanceId))
//      override def getIngredient(recipeInstanceId: String, name: String): G[Value] =
//        mapK(self.getIngredient(recipeInstanceId, name))
      override def getIngredients(recipeInstanceId: String): G[Map[String, Value]] =
        mapK(self.getIngredients(recipeInstanceId))
      override def getEvents(recipeInstanceId: String): G[Seq[EventMoment]] =
        mapK(self.getEvents(recipeInstanceId))
      override def getEventNames(recipeInstanceId: String): G[Seq[String]] =
        mapK(self.getEventNames(recipeInstanceId))
      override def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle): G[String] =
        mapK(self.getVisualState(recipeInstanceId))
      override def registerEventListener(recipeName: String, listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): G[Unit] =
        mapK(self.registerEventListener(recipeName, listenerFunction))
      override def registerEventListener(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): G[Unit] =
        mapK(self.registerEventListener(listenerFunction))
      override def registerBakerEventListener(listenerFunction: BakerEvent => Unit): G[Unit] =
        mapK(self.registerBakerEventListener(listenerFunction))
      override def gracefulShutdown(): G[Unit] =
        mapK(self.gracefulShutdown())
      override def retryInteraction(recipeInstanceId: String, interactionName: String): G[Unit] =
        mapK(self.retryInteraction(recipeInstanceId, interactionName))
      override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): G[Unit] =
        mapK(self.resolveInteraction(recipeInstanceId, interactionName, event))
      override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): G[Unit] =
        mapK(self.stopRetryingInteraction(recipeInstanceId, interactionName))
    }

  def asDeprecatedFutureImplementation(mapK: F ~> Future, comapK: Future ~> F): DeprecatedBaker =
    new DeprecatedBaker {
      override def addRecipe(recipeRecord: RecipeRecord): Future[String] =
        mapK(self.addRecipe(recipeRecord))
      override def getRecipe(recipeId: String): Future[RecipeInformation] =
        mapK(self.getRecipe(recipeId))
      override def getRecipeVisual(recipeId: String, style: RecipeVisualStyle): Future[String] =
        mapK(self.getRecipeVisual(recipeId, style))
      override def getAllRecipes: Future[Map[String, RecipeInformation]] =
        mapK(self.getAllRecipes)
      override def getAllInteractions: Future[Seq[InteractionInstanceDescriptor]] =
        mapK(self.getAllInteractions)
      override def getInteraction(interactionName: String): Future[Option[InteractionInstanceDescriptor]] =
        mapK(self.getInteraction(interactionName))
      override def executeSingleInteraction(interactionId: String, ingredients: Seq[IngredientInstance]): Future[InteractionExecutionResult] =
        mapK(self.executeSingleInteraction(interactionId, ingredients))
      override def bake(recipeId: String, recipeInstanceId: String): Future[Unit] =
        mapK(self.bake(recipeId, recipeInstanceId))
      override def bake(recipeId: String, recipeInstanceId: String, metadata: Map[String, String]): Future[Unit] =
        mapK(self.bake(recipeId, recipeInstanceId, metadata))
      override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): Future[SensoryEventStatus] =
        mapK(self.fireEventAndResolveWhenReceived(recipeInstanceId, event, correlationId))
      override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): Future[SensoryEventResult] =
        mapK(self.fireEventAndResolveWhenCompleted(recipeInstanceId, event, correlationId))
      override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String]): Future[SensoryEventResult] =
        mapK(self.fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, correlationId))
      override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): EventResolutions = {
        val old = self.fireEvent(recipeInstanceId, event, correlationId)
        EventResolutions(mapK(old.resolveWhenReceived), mapK(old.resolveWhenCompleted))
      }
      override def getAllRecipeInstancesMetadata: Future[Set[RecipeInstanceMetadata]] =
        mapK(self.getAllRecipeInstancesMetadata)
      override def getRecipeInstanceState(recipeInstanceId: String): Future[RecipeInstanceState] =
        mapK(self.getRecipeInstanceState(recipeInstanceId))
//      override def getIngredient(recipeInstanceId: String, name: String): Future[Value] =
//        mapK(self.getIngredient(recipeInstanceId, name))
      override def getIngredients(recipeInstanceId: String): Future[Map[String, Value]] =
        mapK(self.getIngredients(recipeInstanceId))
      override def getEvents(recipeInstanceId: String): Future[Seq[EventMoment]] =
        mapK(self.getEvents(recipeInstanceId))
      override def getEventNames(recipeInstanceId: String): Future[Seq[String]] =
        mapK(self.getEventNames(recipeInstanceId))
      override def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle): Future[String] =
        mapK(self.getVisualState(recipeInstanceId, style))
      override def registerEventListener(recipeName: String, listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): Future[Unit] =
        mapK(self.registerEventListener(recipeName, listenerFunction))
      override def registerEventListener(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): Future[Unit] =
        mapK(self.registerEventListener(listenerFunction))
      override def registerBakerEventListener(listenerFunction: BakerEvent => Unit): Future[Unit] =
        mapK(self.registerBakerEventListener(listenerFunction))
      override def gracefulShutdown(): Future[Unit] =
        mapK(self.gracefulShutdown())
      override def retryInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] =
        mapK(self.retryInteraction(recipeInstanceId, interactionName))
      override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): Future[Unit] =
        mapK(self.resolveInteraction(recipeInstanceId, interactionName, event))
      override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] =
        mapK(self.stopRetryingInteraction(recipeInstanceId, interactionName))
      override def addMetaData(recipeInstanceId: String, metadata: Map[String, String]): Future[Unit] =
        mapK(self.addMetaData(recipeInstanceId, metadata))
    }

}
