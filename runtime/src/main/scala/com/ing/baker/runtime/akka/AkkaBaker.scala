package com.ing.baker.runtime.akka

import akka.actor.{Actor, ActorRef, Props}
import akka.pattern.{FutureRef, ask}
import akka.util.Timeout
import com.ing.baker.il._
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.akka.actor._
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol.{Initialized, InstanceState, Uninitialized}
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol
import com.ing.baker.runtime.common.BakerException._
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.types.Value
import org.slf4j.{Logger, LoggerFactory}

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.language.postfixOps
import scala.util.Try

/**
  * The Baker is the component of the Baker library that runs one or multiples recipes.
  * For each recipe a new instance can be baked, sensory events can be send and state can be inquired upon
  */
class AkkaBaker private[runtime](config: AkkaBakerConfig) extends Baker {

  import config.{materializer, system}

  private val log: Logger = LoggerFactory.getLogger(classOf[AkkaBaker])

  val recipeManager: ActorRef =
    config.bakerActorProvider.createRecipeManagerActor()

  val processIndexActor: ActorRef =
    config.bakerActorProvider.createProcessIndexActor(config.interactionManager, recipeManager)

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  override def addRecipe(compiledRecipe: CompiledRecipe): Future[String] = {

    // check if every interaction has an implementation
    val implementationErrors = getImplementationErrors(compiledRecipe)

    if (implementationErrors.nonEmpty)
      Future.failed(ImplementationsException(implementationErrors.mkString(", ")))

    else if (compiledRecipe.validationErrors.nonEmpty)
      Future.failed(RecipeValidationException(compiledRecipe.validationErrors.mkString(", ")))

    else recipeManager.ask(RecipeManagerProtocol.AddRecipe(compiledRecipe))(config.defaultAddRecipeTimeout) flatMap {
      case RecipeManagerProtocol.AddRecipeResponse(recipeId) => Future.successful(recipeId)
    }
  }

  private def getImplementationErrors(compiledRecipe: CompiledRecipe): Set[String] = {
    compiledRecipe.interactionTransitions.filterNot(config.interactionManager.hasImplementation)
      .map(s => s"No implementation provided for interaction: ${s.originalInteractionName}")
  }

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  override def getRecipe(recipeId: String): Future[RecipeInformation] = {
    // here we ask the RecipeManager actor to return us the recipe for the given id
    recipeManager.ask(RecipeManagerProtocol.GetRecipe(recipeId))(config.defaultInquireTimeout).flatMap {
      case RecipeManagerProtocol.RecipeFound(compiledRecipe, timestamp) =>
        Future.successful(RecipeInformation(compiledRecipe, timestamp, getImplementationErrors(compiledRecipe)))
      case RecipeManagerProtocol.NoRecipeFound(_) =>
        Future.failed(NoSuchRecipeException(recipeId))
    }
  }

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes: Future[Map[String, RecipeInformation]] =
    recipeManager.ask(RecipeManagerProtocol.GetAllRecipes)(config.defaultInquireTimeout)
      .mapTo[RecipeManagerProtocol.AllRecipes]
      .map(_.recipes.map { ri =>
        ri.compiledRecipe.recipeId -> RecipeInformation(ri.compiledRecipe, ri.timestamp, getImplementationErrors(ri.compiledRecipe))
      }.toMap)

  /**
    * Creates a process instance for the given recipeId with the given RecipeInstanceId as identifier
    *
    * @param recipeId  The recipeId for the recipe to bake
    * @param recipeInstanceId The identifier for the newly baked process
    * @return
    */
  override def bake(recipeId: String, recipeInstanceId: String): Future[Unit] = {
    processIndexActor.ask(CreateProcess(recipeId, recipeInstanceId))(config.defaultBakeTimeout).flatMap {
      case _: Initialized =>
        Future.successful(())
      case ProcessAlreadyExists(_) =>
        Future.failed(ProcessAlreadyExistsException(recipeInstanceId))
      case RecipeManagerProtocol.NoRecipeFound(_) =>
        Future.failed(NoSuchRecipeException(recipeId))
    }
  }

  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: Option[String]): Future[SensoryEventStatus] =
    processIndexActor.ask(ProcessEvent(
      recipeInstanceId = recipeInstanceId,
      event = event,
      correlationId = correlationId,
      timeout = config.defaultProcessEventTimeout,
      reaction = FireSensoryEventReaction.NotifyWhenReceived
    ))(config.defaultProcessEventTimeout).flatMap {
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
      timeout = config.defaultProcessEventTimeout,
      reaction = FireSensoryEventReaction.NotifyWhenCompleted(waitForRetries = true)
    ))(config.defaultProcessEventTimeout).flatMap {
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
      timeout = config.defaultProcessEventTimeout,
      reaction = FireSensoryEventReaction.NotifyOnEvent(waitForRetries = true, onEvent)
    ))(config.defaultProcessEventTimeout).flatMap {
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
    val futureRef = FutureRef(config.defaultProcessEventTimeout)
    val futureReceived =
      processIndexActor.ask(ProcessEvent(
        recipeInstanceId = recipeInstanceId,
        event = event,
        correlationId = correlationId,
        timeout = config.defaultProcessEventTimeout,
        reaction = FireSensoryEventReaction.NotifyBoth(
          waitForRetries = true,
          completeReceiver = futureRef.ref)
      ))(config.defaultProcessEventTimeout).flatMap {
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
      futureRef.future.flatMap {
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

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  override def retryInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] = {
    processIndexActor.ask(RetryBlockedInteraction(recipeInstanceId, interactionName))(config.defaultProcessEventTimeout).map(_ => ())
  }

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(recipeInstanceId: String, interactionName: String, event: EventInstance): Future[Unit] = {
    processIndexActor.ask(ResolveBlockedInteraction(recipeInstanceId, interactionName, event))(config.defaultProcessEventTimeout).map(_ => ())
  }

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(recipeInstanceId: String, interactionName: String): Future[Unit] = {
    processIndexActor.ask(StopRetryingInteraction(recipeInstanceId, interactionName))(config.defaultProcessEventTimeout).map(_ => ())
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
    Future.successful(config.bakerActorProvider
      .getAllProcessesMetadata(processIndexActor)(system, config.defaultInquireTimeout)
      .map(p => RecipeInstanceMetadata(p.recipeId, p.recipeInstanceId, p.createdDateTime)).toSet)
  }

  /**
    * Returns the process state.
    *
    * @param recipeInstanceId The process identifier
    * @return The process state.
    */
  override def getRecipeInstanceState(recipeInstanceId: String): Future[RecipeInstanceState] =
    processIndexActor
      .ask(GetProcessState(recipeInstanceId))(Timeout.durationToTimeout(config.defaultInquireTimeout))
      .flatMap {
        case instance: InstanceState => Future.successful(instance.state.asInstanceOf[RecipeInstanceState])
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
      getRecipeResponse <- processIndexActor.ask(GetCompiledRecipe(recipeInstanceId))(config.defaultInquireTimeout)
      processState <- getRecipeInstanceState(recipeInstanceId)
      response <- getRecipeResponse match {
        case RecipeManagerProtocol.RecipeFound(compiledRecipe, _) =>
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

  private def doRegisterEventListener(listenerFunction: (String, EventInstance) => Unit, processFilter: String => Boolean): Future[Unit] = {
    registerBakerEventListener {
      case EventReceived(_, recipeName, _, recipeInstanceId, _, event) if processFilter(recipeName) =>
        listenerFunction.apply(recipeInstanceId, event)
      case InteractionCompleted(_, _, recipeName, _, recipeInstanceId, _, Some(event)) if processFilter(recipeName) =>
        listenerFunction.apply(recipeInstanceId, event)
      case InteractionFailed(_, _, recipeName, _, recipeInstanceId, _, _, _, ExceptionStrategyOutcome.Continue(eventName)) if processFilter(recipeName) =>
        listenerFunction.apply(recipeInstanceId, EventInstance(eventName, Map.empty))
      case _ => ()
    }
  }

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(recipeName: String, listenerFunction: (String, EventInstance) => Unit): Future[Unit] =
    doRegisterEventListener(listenerFunction, _ == recipeName)

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  //  @deprecated("Use event bus instead", "1.4.0")
  override def registerEventListener(listenerFunction: (String, EventInstance) => Unit): Future[Unit] =
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
            log.warn(s"Listener function threw exception for event: $event", e)
          }
        }
      }))
      system.eventStream.subscribe(listenerActor, classOf[BakerEvent])
    }
  }

  /**
    * Adds an interaction implementation to baker.
    *
    * This is assumed to be a an object with a method named 'apply' defined on it.
    *
    * @param implementation The implementation object
    */
  override def addInteractionInstance(implementation: InteractionInstance): Future[Unit] =
    Future.successful(config.interactionManager.addImplementation(implementation))

  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  override def addInteractionInstances(implementations: Seq[InteractionInstance]): Future[Unit] =
    Future.successful(implementations.foreach(addInteractionInstance))

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown: Future[Unit] =
    Future.successful(GracefulShutdown.gracefulShutdownActorSystem(system, config.defaultShutdownTimeout))
}
