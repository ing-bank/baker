package com.ing.baker.runtime.akka

import akka.actor.{Actor, ActorRef, ActorSystem, Address, Props}
import akka.pattern.{FutureRef, ask}
import akka.util.Timeout
import cats.data.NonEmptyList
import cats.implicits._
import com.ing.baker.il._
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.akka.actor._
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol.{Initialized, InstanceState, MetaDataAdded, Uninitialized}
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol.RecipeFound
import com.ing.baker.runtime.akka.internal.CachingInteractionManager
import com.ing.baker.runtime.common.BakerException._
import com.ing.baker.runtime.common.{InteractionExecutionFailureReason, RecipeRecord, SensoryEventStatus}
import com.ing.baker.runtime.recipe_manager.{ActorBasedRecipeManager, DefaultRecipeManager, RecipeManager}
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.runtime.{javadsl, scaladsl}
import com.ing.baker.types.Value
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import net.ceedubs.ficus.Ficus._

import java.util.{List => JavaList}
import scala.annotation.nowarn
import scala.collection.immutable.Seq
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.language.postfixOps
import scala.util.Try

object AkkaBaker {

  def apply(config: Config, actorSystem: ActorSystem, interactions: CachingInteractionManager, recipeManager: RecipeManager): scaladsl.Baker =
    new AkkaBaker(AkkaBakerConfig.from(config, actorSystem, interactions, recipeManager))

  def apply(config: Config, actorSystem: ActorSystem, interactions: CachingInteractionManager): scaladsl.Baker =
    new AkkaBaker(AkkaBakerConfig.from(config, actorSystem, interactions, determineRecipeManager(config)(actorSystem)))

  def apply(config: AkkaBakerConfig): AkkaBaker =
    new AkkaBaker(config)

  def localDefault(actorSystem: ActorSystem, interactions: CachingInteractionManager): scaladsl.Baker =
    new AkkaBaker(AkkaBakerConfig.localDefault(actorSystem, interactions))

  def clusterDefault(seedNodes: NonEmptyList[Address], actorSystem: ActorSystem, interactions: CachingInteractionManager): scaladsl.Baker =
    new AkkaBaker(AkkaBakerConfig.clusterDefault(seedNodes, actorSystem, interactions))

  def java(config: Config, actorSystem: ActorSystem, interactions: CachingInteractionManager, recipeManager: RecipeManager): javadsl.Baker =
    new javadsl.Baker(com.ing.baker.runtime.akka.AkkaBaker.apply(config, actorSystem, interactions, recipeManager))

  def java(config: Config, actorSystem: ActorSystem): javadsl.Baker =
    new javadsl.Baker(com.ing.baker.runtime.akka.AkkaBaker.apply(config, actorSystem, CachingInteractionManager(), DefaultRecipeManager.pollingAware(actorSystem.dispatcher)))

  def java(config: Config, actorSystem: ActorSystem, interactions: JavaList[AnyRef]): javadsl.Baker =
    new javadsl.Baker(com.ing.baker.runtime.akka.AkkaBaker.apply(config, actorSystem,
      CachingInteractionManager.fromJava(interactions, config.getOrElse[Boolean]("baker.interactions.allow-superset-for-output-types", false))))

  def java(config: AkkaBakerConfig): javadsl.Baker =
    new javadsl.Baker(com.ing.baker.runtime.akka.AkkaBaker.apply(config))

  //Used for backwards compatability reasons to ensure it works the same as before the RecipeManager was provided
  private def determineRecipeManager(config: Config)(implicit actorSystem: ActorSystem): RecipeManager = {
    if (config.hasPath("baker.recipe-manager-type") && config.getString("baker.recipe-manager-type") == "inmemory")
      DefaultRecipeManager.pollingAware(actorSystem.dispatcher)
    else ActorBasedRecipeManager.getRecipeManagerActor(actorSystem, config)
  }
}

/**
  * The Baker is the component of the Baker library that runs one or multiples recipes.
  * For each recipe a new instance can be baked, sensory events can be send and state can be inquired upon
  */
class AkkaBaker private[runtime](config: AkkaBakerConfig) extends scaladsl.Baker with LazyLogging {
  import config.system

  config.bakerActorProvider.initialize(system)

  private val recipeManager: RecipeManager =
    config.recipeManager

  private val processIndexActor: ActorRef =
    config.bakerActorProvider.createProcessIndexActor(config.interactions, recipeManager, system.settings.config)

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param recipeRecord RecipeRecord of the Recipe.
    * @return A recipeId
    */
  override def addRecipe(recipeRecord: RecipeRecord): Future[String] = for {
    _ <- config.interactions.recipeAdded(recipeRecord).unsafeToFuture()
    result <- {
      val recipe = recipeRecord.recipe
      val updated = recipeRecord.updated
      if (!recipeRecord.validate || config.bakerValidationSettings.allowAddingRecipeWithoutRequiringInstances) {
        logger.debug(s"Recipe implementation errors are ignored for ${recipe.name}:${recipe.recipeId}")
        addToManager(recipe, updated)
      } else {
        logger.debug(s"Recipe ${recipe.name}:${recipe.recipeId} is validated for compatibility with interactions")
        getImplementationErrors(recipe).flatMap { implementationErrors =>
          if (implementationErrors.nonEmpty) {
            Future.failed(ImplementationsException(s"Recipe ${recipe.name}:${recipe.recipeId} has implementation errors: ${implementationErrors.mkString(", ")}"))
          } else if (recipe.validationErrors.nonEmpty) {
            Future.failed(RecipeValidationException(s"Recipe ${recipe.name}:${recipe.recipeId} has validation errors: ${recipe.validationErrors.mkString(", ")}"))
          } else {
            addToManager(recipe, updated)
          }
        }
      }
    }
  } yield result

  private def addToManager(compiledRecipe: CompiledRecipe, timeCreated: Long): Future[String] =
    recipeManager.put(RecipeRecord.of(compiledRecipe, updated = timeCreated))

  private def getImplementationErrors(compiledRecipe: CompiledRecipe): Future[Set[String]] = {
    compiledRecipe.interactionTransitions.toList
      .traverse(x => config.interactions.incompatibilities(x).map((_, x.originalInteractionName)))
      .map(_
        .filterNot(_._1.isEmpty)
        .map(x => s"No compatible implementation provided for interaction: ${x._2}: ${x._1}")
        .toSet)
  }.unsafeToFuture()

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  override def getRecipe(recipeId: String): Future[RecipeInformation] = {
    // here we ask the RecipeManager actor to return us the recipe for the given id
    recipeManager.get(recipeId).flatMap {
      case Some(r: RecipeRecord) =>
        getImplementationErrors(r.recipe).map(errors => RecipeInformation(r.recipe, r.updated, errors, r.validate ))
      case None =>
        Future.failed(NoSuchRecipeException(recipeId))
    }
  }


  override def getRecipeVisual(recipeId: String, style: RecipeVisualStyle = RecipeVisualStyle.default): Future[String] =
    getRecipe(recipeId).map(r => RecipeVisualizer.visualizeRecipe(r.compiledRecipe, style))

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes: Future[Map[String, RecipeInformation]] = {
    recipeManager.all
      .flatMap(
        _.toList
          .traverse(ri => getImplementationErrors(ri.recipe)
            .map(errors => ri.recipeId -> RecipeInformation(ri.recipe, ri.updated, errors, ri.validate))
          ).map(_.toMap)
      )
  }


  override def getInteraction(interactionName: String): Future[Option[InteractionInstanceDescriptor]] =
    config.interactions.listAll.map(
      _.find(_.name == interactionName)
        .map(i => InteractionInstanceDescriptor(i.shaBase64, i.name, i.input, i.output))).unsafeToFuture()


  override def getAllInteractions: Future[List[InteractionInstanceDescriptor]] =
    config.interactions.listAll.map(_.map(
      i => InteractionInstanceDescriptor(i.shaBase64, i.name, i.input, i.output))).unsafeToFuture()

  override def executeSingleInteraction(interactionId: String, ingredients: Seq[IngredientInstance]): Future[InteractionExecutionResult] =
    config.interactions
      .listAll
      .map(interactionsList => interactionsList.find(_.shaBase64 == interactionId))
      .flatMap {
        case None => cats.effect.IO.pure(InteractionExecutionResult(Left(InteractionExecutionResult.Failure(
          InteractionExecutionFailureReason.INTERACTION_NOT_FOUND, None, None))))
        case Some(interactionInstance) =>
          interactionInstance.execute(ingredients, Map())
            .map(executionSuccess => InteractionExecutionResult(Right(InteractionExecutionResult.Success(executionSuccess))))
            .recover {
              case e => InteractionExecutionResult(Left(InteractionExecutionResult.Failure(
                InteractionExecutionFailureReason.INTERACTION_EXECUTION_ERROR,
                Some(interactionInstance.name),
                Some(s"Interaction execution failed. Interaction threw ${e.getClass.getSimpleName} with message ${e.getMessage}."))))
            }
            .timeoutTo(duration = config.timeouts.defaultExecuteSingleInteractionTimeout,
              fallback = cats.effect.IO.pure(
                InteractionExecutionResult(Left(
                  InteractionExecutionResult.Failure(InteractionExecutionFailureReason.TIMEOUT, Some(interactionInstance.name), None)))))(
              timer = cats.effect.IO.timer(config.system.dispatcher), cs = cats.effect.IO.contextShift(config.system.dispatcher))
      }
      .unsafeToFuture().javaTimeoutToBakerTimeout("executeSingleInteraction")

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    *
    * @param recipeId         The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @return
    */
  override def bake(recipeId: String, recipeInstanceId: String): Future[Unit] = {
    processIndexActor.ask(CreateProcess(recipeId, recipeInstanceId))(config.timeouts.defaultBakeTimeout).javaTimeoutToBakerTimeout("bake").flatMap {
      case _: Initialized =>
        Future.successful(())
      case ProcessAlreadyExists(_) =>
        Future.failed(ProcessAlreadyExistsException(recipeInstanceId))
      case RecipeManagerProtocol.NoRecipeFound(_) =>
        Future.failed(NoSuchRecipeException(recipeId))
    }
  }

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    * This variant also gets a metadata map added on bake.
    * This is similar to calling addMetaData after doing the regular bake but depending on the implementation this can be more optimized.
    *
    * @param recipeId         The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @param metadata
    * @return
    */
  override def bake(recipeId: String, recipeInstanceId: String, metadata: Map[String, String]): Future[Unit] = {
    bake(recipeId, recipeInstanceId).map(_ -> addMetaData(recipeInstanceId, metadata))
  }

  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): Future[SensoryEventStatus] =
    processIndexActor.ask(ProcessEvent(
      recipeInstanceId = recipeInstanceId,
      event = event,
      correlationId = correlationId,
      timeout = config.timeouts.defaultProcessEventTimeout,
      reaction = FireSensoryEventReaction.NotifyWhenReceived
    ))(config.timeouts.defaultProcessEventTimeout).javaTimeoutToBakerTimeout("fireEventAndResolveWhenReceived").flatMap {
      // TODO MOVE THIS TO A FUNCTION
      case FireSensoryEventRejection.InvalidEvent(_, message) =>
        Future.failed(IllegalEventException(message))
      case FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0) =>
        Future.failed(NoSuchProcessException(recipeInstanceId0))
      case _: FireSensoryEventRejection.FiringLimitMet =>
        Future.successful(SensoryEventStatus.FiringLimitMet)
      case _: FireSensoryEventRejection.AlreadyReceived =>
        Future.successful(SensoryEventStatus.AlreadyReceived)
      case _: FireSensoryEventRejection.ReceivePeriodExpired =>
        Future.successful(SensoryEventStatus.ReceivePeriodExpired)
      case _: FireSensoryEventRejection.RecipeInstanceDeleted =>
        Future.successful(SensoryEventStatus.RecipeInstanceDeleted)
      case ProcessEventReceivedResponse(status) =>
        Future.successful(status)
    }

  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): Future[SensoryEventResult] =
    processIndexActor.ask(ProcessEvent(
      recipeInstanceId = recipeInstanceId,
      event = event,
      correlationId = correlationId,
      timeout = config.timeouts.defaultProcessEventTimeout,
      reaction = FireSensoryEventReaction.NotifyWhenCompleted(waitForRetries = true)
    ))(config.timeouts.defaultProcessEventTimeout).javaTimeoutToBakerTimeout("fireEventAndResolveWhenCompleted").flatMap {
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

  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstanceType, onEvent: String, correlationId: Option[String]): Future[SensoryEventResult] =
    processIndexActor.ask(ProcessEvent(
      recipeInstanceId = recipeInstanceId,
      event = event,
      correlationId = correlationId,
      timeout = config.timeouts.defaultProcessEventTimeout,
      reaction = FireSensoryEventReaction.NotifyOnEvent(waitForRetries = true, onEvent)
    ))(config.timeouts.defaultProcessEventTimeout).javaTimeoutToBakerTimeout("fireEventAndResolveOnEvent").flatMap {
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

  override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): EventResolutions = {
    val futureRef = FutureRef(config.timeouts.defaultProcessEventTimeout)
    val futureReceived =
      processIndexActor.ask(ProcessEvent(
        recipeInstanceId = recipeInstanceId,
        event = event,
        correlationId = correlationId,
        timeout = config.timeouts.defaultProcessEventTimeout,
        reaction = FireSensoryEventReaction.NotifyBoth(
          waitForRetries = true,
          completeReceiver = futureRef.ref)
      ))(config.timeouts.defaultProcessEventTimeout).javaTimeoutToBakerTimeout("fireEvent").flatMap {
        case FireSensoryEventRejection.InvalidEvent(_, message) =>
          Future.failed(IllegalEventException(message))
        case FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0) =>
          Future.failed(NoSuchProcessException(recipeInstanceId0))
        case _: FireSensoryEventRejection.FiringLimitMet =>
          Future.successful(SensoryEventStatus.FiringLimitMet)
        case _: FireSensoryEventRejection.AlreadyReceived =>
          Future.successful(SensoryEventStatus.AlreadyReceived)
        case _: FireSensoryEventRejection.ReceivePeriodExpired =>
          Future.successful(SensoryEventStatus.ReceivePeriodExpired)
        case _: FireSensoryEventRejection.RecipeInstanceDeleted =>
          Future.successful(SensoryEventStatus.RecipeInstanceDeleted)
        case ProcessEventReceivedResponse(status) =>
          Future.successful(status)
      }
    val futureCompleted =
      futureRef.future.javaTimeoutToBakerTimeout("fireEvent").flatMap {
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
    EventResolutions(futureReceived, futureCompleted)
  }

  override def addMetaData(recipeInstanceId: String, metadata: Map[String, String]): Future[Unit] = {
    processIndexActor
      .ask(AddRecipeInstanceMetaData(recipeInstanceId, metadata))(Timeout.durationToTimeout(config.timeouts.defaultInquireTimeout))
      .flatMap {
        case MetaDataAdded => Future.successful(())
        case Uninitialized(id) => Future.failed(NoSuchProcessException(id))
        case NoSuchProcess(id) => Future.failed(NoSuchProcessException(id))
        case ProcessDeleted(id) => Future.failed(ProcessDeletedException(id))
      }
  }

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  override def retryInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] = {
    processIndexActor.ask(RetryBlockedInteraction(recipeInstanceId, interactionName))(config.timeouts.defaultProcessEventTimeout).javaTimeoutToBakerTimeout("retryInteraction").map(_ => ())
  }

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): Future[Unit] = {
    processIndexActor.ask(ResolveBlockedInteraction(recipeInstanceId, interactionName, event))(config.timeouts.defaultProcessEventTimeout).javaTimeoutToBakerTimeout("resolveInteraction").map(_ => ())
  }

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] = {
    processIndexActor.ask(StopRetryingInteraction(recipeInstanceId, interactionName))(config.timeouts.defaultProcessEventTimeout).javaTimeoutToBakerTimeout("stopRetryingInteraction").map(_ => ())
  }

  /**
    * Returns an index of all processes.
    *
    * Can potentially return a partial index when baker runs in cluster mode
    * and not all shards can be reached within the given timeout.
    *
    * Does not include deleted processes.
    *
    * @return An index of all processes
    */
  override def getAllRecipeInstancesMetadata: Future[Set[RecipeInstanceMetadata]] = {
    Future(config.bakerActorProvider
      .getAllProcessesMetadata(processIndexActor)(system, config.timeouts.defaultInquireTimeout)
      .map(p => RecipeInstanceMetadata(p.recipeId, p.recipeInstanceId, p.createdDateTime)).toSet)
      .javaTimeoutToBakerTimeout("getAllRecipeInstancesMetadata")
  }

  /**
    * Returns the process state.
    *
    * @param recipeInstanceId The process identifier
    * @return The process state.
    */
  override def getRecipeInstanceState(recipeInstanceId: String): Future[RecipeInstanceState] =
    processIndexActor
      .ask(GetProcessState(recipeInstanceId))(Timeout.durationToTimeout(config.timeouts.defaultInquireTimeout))
      .javaTimeoutToBakerTimeout("getRecipeInstanceState")
      .flatMap {
        case instance: InstanceState => Future.successful(instance.state.asInstanceOf[RecipeInstanceState])
        case Uninitialized(id) => Future.failed(NoSuchProcessException(id))
        case NoSuchProcess(id) => Future.failed(NoSuchProcessException(id))
        case ProcessDeleted(id) => Future.failed(ProcessDeletedException(id))
      }

  /**
    * Returns all provided ingredients for a given process id.
    *
    * @param recipeInstanceId The process id.
    * @return The provided ingredients.
    */
  override def getIngredients(recipeInstanceId: String): Future[Map[String, Value]] =
    getRecipeInstanceState(recipeInstanceId).map(_.ingredients)

  /**
    * Returns all fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The events
    */
  override def getEvents(recipeInstanceId: String): Future[Seq[EventMoment]] =
    getRecipeInstanceState(recipeInstanceId).map(_.events)

  /**
    * Returns all names of fired events for a given RecipeInstance id.
    *
    * @param recipeInstanceId The process id.
    * @return The event names
    */
  override def getEventNames(recipeInstanceId: String): Future[Seq[String]] =
    getRecipeInstanceState(recipeInstanceId).map(_.eventNames)

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param recipeInstanceId The process identifier.
    * @return A visual (.dot) representation of the process state.
    */
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  override def getVisualState(recipeInstanceId: String, style: RecipeVisualStyle = RecipeVisualStyle.default): Future[String] = {
    for {
      getRecipeResponse <- processIndexActor.ask(GetCompiledRecipe(recipeInstanceId))(config.timeouts.defaultInquireTimeout).javaTimeoutToBakerTimeout("getVisualState")
      processState <- getRecipeInstanceState(recipeInstanceId)
      response <- getRecipeResponse match {
        case RecipeFound(compiledRecipe, _) =>
          Future.successful(RecipeVisualizer.visualizeRecipe(
            compiledRecipe,
            style,
            eventNames = processState.eventNames.toSet,
            ingredientNames = processState.ingredients.keySet))
        case ProcessDeleted(_) =>
          Future.failed(ProcessDeletedException(recipeInstanceId))
        case Uninitialized(_) =>
          Future.failed(NoSuchProcessException(recipeInstanceId))
      }
    } yield response
  }

  private def doRegisterEventListener(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit, processFilter: String => Boolean): Future[Unit] = {
    registerBakerEventListener {
      case EventReceived(_, recipeName, recipeId, recipeInstanceId, _, event) if processFilter(recipeName) =>
        listenerFunction.apply(RecipeEventMetadata(recipeId = recipeId, recipeName = recipeName, recipeInstanceId = recipeInstanceId), event)
      case InteractionCompleted(_, _, recipeName, recipeId, recipeInstanceId, _, Some(event)) if processFilter(recipeName) =>
        listenerFunction.apply(RecipeEventMetadata(recipeId = recipeId, recipeName = recipeName, recipeInstanceId = recipeInstanceId), event)
      case InteractionFailed(_, _, recipeName, recipeId, recipeInstanceId, _, _, _, ExceptionStrategyOutcome.Continue(eventName)) if processFilter(recipeName) =>
        listenerFunction.apply(RecipeEventMetadata(recipeId = recipeId, recipeName = recipeName, recipeInstanceId = recipeInstanceId), EventInstance(eventName, Map.empty))
      case _ => ()
    }
  }

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(recipeName: String, listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): Future[Unit] =
    doRegisterEventListener(listenerFunction, _ == recipeName)

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  //  @deprecated("Use event bus instead", "1.4.0")
  override def registerEventListener(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): Future[Unit] =
    doRegisterEventListener(listenerFunction, _ => true)

  /**
    * Registers a listener function that listens to all BakerEvents
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    *
    * @param listenerFunction
    * @return
    */
  override def registerBakerEventListener(listenerFunction: BakerEvent => Unit): Future[Unit] = {
    Future.successful {
      val listenerActor = system.actorOf(Props(new Actor() {
        override def receive: Receive = {
          case event: BakerEvent => Try {
            listenerFunction.apply(event)
          }.failed.foreach { e =>
            logger.warn(s"Listener function threw exception for event: $event", e)
          }
        }
      }))
      system.eventStream.subscribe(listenerActor, classOf[BakerEvent])
    }
  }

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  @nowarn
  override def gracefulShutdown(): Future[Unit] =
    GracefulShutdown.gracefulShutdownActorSystem(system, config.timeouts.defaultShutdownTimeout, config.terminateActorSystem)
      .javaTimeoutToBakerTimeout("gracefulShutdown").map(_ => ())
}
