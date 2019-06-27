package com.ing.baker.runtime.akka

import akka.actor.{Actor, ActorRef, Props}
import akka.pattern.{FutureRef, ask}
import akka.util.Timeout
import com.ing.baker.il._
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.akka.actor._
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol.{Initialized, InstanceState, Uninitialized}
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.{ProcessMetadata, SensoryEventStatus}
import com.ing.baker.runtime.common.BakerException._
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
      Future.failed(new ImplementationsException(implementationErrors.mkString(", ")))

    else if (compiledRecipe.validationErrors.nonEmpty)
      Future.failed(new RecipeValidationException(compiledRecipe.validationErrors.mkString(", ")))

    else recipeManager.ask(AddRecipe(compiledRecipe))(config.defaultAddRecipeTimeout) flatMap {
      case AddRecipeResponse(recipeId) => Future.successful(recipeId)
    }
  }

  private def getImplementationErrors(compiledRecipe: CompiledRecipe): Set[String] = {
    compiledRecipe.interactionTransitions.filterNot(config.interactionManager.getImplementation(_).isDefined)
      .map(s => s"No implementation provided for interaction: ${s.originalInteractionName}")
  }

  /**
    * Returns the recipe information for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  override def getRecipe(recipeId: String): Future[common.RecipeInformation] = {
    // here we ask the RecipeManager actor to return us the recipe for the given id
    recipeManager.ask(GetRecipe(recipeId))(config.defaultInquireTimeout).flatMap {
      case RecipeFound(compiledRecipe, timestamp) =>
        Future.successful(common.RecipeInformation(compiledRecipe, timestamp, getImplementationErrors(compiledRecipe)))
      case NoRecipeFound(_) =>
        Future.failed(new IllegalArgumentException(s"No recipe found for recipe with id: $recipeId"))
    }
  }

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  override def getAllRecipes: Future[Map[String, common.RecipeInformation]] =
    recipeManager.ask(GetAllRecipes)(config.defaultInquireTimeout)
      .mapTo[AllRecipes]
      .map(_.recipes.map { ri =>
        ri.compiledRecipe.recipeId -> common.RecipeInformation(ri.compiledRecipe, ri.timestamp, getImplementationErrors(ri.compiledRecipe))
      }.toMap)

  /**
    * Creates a process instance for the given recipeId with the given processId as identifier
    *
    * @param recipeId  The recipeId for the recipe to bake
    * @param processId The identifier for the newly baked process
    * @return
    */
  override def bake(recipeId: String, processId: String): Future[Unit] = {
    processIndexActor.ask(CreateProcess(recipeId, processId))(config.defaultBakeTimeout).flatMap {
      case _: Initialized =>
        Future.successful(())
      case ProcessAlreadyExists(_) =>
        Future.failed(new IllegalArgumentException(s"Process with id '$processId' already exists."))
      case NoRecipeFound(_) =>
        Future.failed(new IllegalArgumentException(s"Recipe with id '$recipeId' does not exist."))
    }
  }

  def fireSensoryEventReceived(processId: String, event: RuntimeEvent, correlationId: Option[String]): Future[SensoryEventStatus] =
    processIndexActor.ask(ProcessEvent(
      processId = processId,
      event = event,
      correlationId = correlationId,
      timeout = config.defaultProcessEventTimeout,
      reaction = FireSensoryEventReaction.NotifyWhenReceived
    ))(config.defaultProcessEventTimeout).flatMap {
      // TODO MOVE THIS TO A FUNCTION
      case FireSensoryEventRejection.InvalidEvent(_, message) =>
        Future.failed(new IllegalArgumentException(message))
      case FireSensoryEventRejection.NoSuchProcess(processId0) =>
        Future.failed(new NoSuchProcessException(s"Process with id $processId0 does not exist in the index"))
      case _: FireSensoryEventRejection.FiringLimitMet =>
        Future.successful(SensoryEventStatus.FiringLimitMet)
      case _: FireSensoryEventRejection.AlreadyReceived =>
        Future.successful(SensoryEventStatus.AlreadyReceived)
      case _: FireSensoryEventRejection.ReceivePeriodExpired =>
        Future.successful(SensoryEventStatus.ReceivePeriodExpired)
      case _: FireSensoryEventRejection.ProcessDeleted =>
        Future.successful(SensoryEventStatus.ProcessDeleted)
      case ProcessEventReceivedResponse(status) =>
        Future.successful(status)
    }

  def fireSensoryEventCompleted(processId: String, event: RuntimeEvent, correlationId: Option[String]): Future[SensoryEventResult] =
    processIndexActor.ask(ProcessEvent(
      processId = processId,
      event = event,
      correlationId = correlationId,
      timeout = config.defaultProcessEventTimeout,
      reaction = FireSensoryEventReaction.NotifyWhenCompleted(waitForRetries = true)
    ))(config.defaultProcessEventTimeout).flatMap {
      case FireSensoryEventRejection.InvalidEvent(_, message) =>
        Future.failed(new IllegalArgumentException(message))
      case FireSensoryEventRejection.NoSuchProcess(processId0) =>
        Future.failed(new NoSuchProcessException(s"Process with id $processId0 does not exist in the index"))
      case _: FireSensoryEventRejection.FiringLimitMet =>
        Future.successful(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
      case _: FireSensoryEventRejection.AlreadyReceived =>
        Future.successful(SensoryEventResult(SensoryEventStatus.AlreadyReceived, Seq.empty, Map.empty))
      case _: FireSensoryEventRejection.ReceivePeriodExpired =>
        Future.successful(SensoryEventResult(SensoryEventStatus.ReceivePeriodExpired, Seq.empty, Map.empty))
      case _: FireSensoryEventRejection.ProcessDeleted =>
        Future.successful(SensoryEventResult(SensoryEventStatus.ProcessDeleted, Seq.empty, Map.empty))
      case ProcessEventCompletedResponse(result) =>
        Future.successful(result)
    }

  def fireSensoryEvent(processId: String, event: RuntimeEvent, correlationId: Option[String]): SensoryEventMoments = {
    val futureRef = FutureRef(config.defaultProcessEventTimeout)
    val futureReceived =
      processIndexActor.ask(ProcessEvent(
        processId = processId,
        event = event,
        correlationId = correlationId,
        timeout = config.defaultProcessEventTimeout,
        reaction = FireSensoryEventReaction.NotifyBoth(
          waitForRetries = true,
          completeReceiver = futureRef.ref)
      ))(config.defaultProcessEventTimeout).flatMap {
        case FireSensoryEventRejection.InvalidEvent(_, message) =>
          Future.failed(new IllegalArgumentException(message))
        case FireSensoryEventRejection.NoSuchProcess(processId0) =>
          Future.failed(new NoSuchProcessException(s"Process with id $processId0 does not exist in the index"))
        case _: FireSensoryEventRejection.FiringLimitMet =>
          Future.successful(SensoryEventStatus.FiringLimitMet)
        case _: FireSensoryEventRejection.AlreadyReceived =>
          Future.successful(SensoryEventStatus.AlreadyReceived)
        case _: FireSensoryEventRejection.ReceivePeriodExpired =>
          Future.successful(SensoryEventStatus.ReceivePeriodExpired)
        case _: FireSensoryEventRejection.ProcessDeleted =>
          Future.successful(SensoryEventStatus.ProcessDeleted)
        case ProcessEventReceivedResponse(status) =>
          Future.successful(status)
      }
    val futureCompleted =
      futureRef.future.flatMap {
        case FireSensoryEventRejection.InvalidEvent(_, message) =>
          Future.failed(new IllegalArgumentException(message))
        case FireSensoryEventRejection.NoSuchProcess(processId0) =>
          Future.failed(new NoSuchProcessException(s"Process with id $processId0 does not exist in the index"))
        case _: FireSensoryEventRejection.FiringLimitMet =>
          Future.successful(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
        case _: FireSensoryEventRejection.AlreadyReceived =>
          Future.successful(SensoryEventResult(SensoryEventStatus.AlreadyReceived, Seq.empty, Map.empty))
        case _: FireSensoryEventRejection.ReceivePeriodExpired =>
          Future.successful(SensoryEventResult(SensoryEventStatus.ReceivePeriodExpired, Seq.empty, Map.empty))
        case _: FireSensoryEventRejection.ProcessDeleted =>
          Future.successful(SensoryEventResult(SensoryEventStatus.ProcessDeleted, Seq.empty, Map.empty))
        case ProcessEventCompletedResponse(result) =>
          Future.successful(result)
      }
    SensoryEventMoments(futureReceived, futureCompleted)
  }

  /**
    * Retries a blocked interaction.
    *
    * @return
    */
  override def retryInteraction(processId: String, interactionName: String): Future[Unit] = {
    processIndexActor.ask(RetryBlockedInteraction(processId, interactionName))(config.defaultProcessEventTimeout).map(_ => ())
  }

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(processId: String, interactionName: String, event: RuntimeEvent): Future[Unit] = {
    processIndexActor.ask(ResolveBlockedInteraction(processId, interactionName, event))(config.defaultProcessEventTimeout).map(_ => ())
  }

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(processId: String, interactionName: String): Future[Unit] = {
    processIndexActor.ask(StopRetryingInteraction(processId, interactionName))(config.defaultProcessEventTimeout).map(_ => ())
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
  override def getIndex: Future[Set[ProcessMetadata]] = {
    Future.successful(config.bakerActorProvider
      .getIndex(processIndexActor)(system, config.defaultInquireTimeout)
      .map(p => ProcessMetadata(p.recipeId, p.processId, p.createdDateTime)).toSet)
  }

  /**
    * Returns the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  override def getProcessState(processId: String): Future[ProcessState] =
    processIndexActor
      .ask(GetProcessState(processId))(Timeout.durationToTimeout(config.defaultInquireTimeout))
      .flatMap {
        case instance: InstanceState => Future.successful(instance.state.asInstanceOf[ProcessState])
        case NoSuchProcess(id) => Future.failed(new NoSuchProcessException(s"No such process with: $id"))
        case ProcessDeleted(id) => Future.failed(new ProcessDeletedException(s"Process $id is deleted"))
      }

  /**
    * Returns all provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return The provided ingredients.
    */
  override def getIngredients(processId: String): Future[Map[String, Value]] =
    getProcessState(processId).map(_.ingredients)

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param processId The process identifier.
    * @return A visual (.dot) representation of the process state.
    */
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  override def getVisualState(processId: String, style: RecipeVisualStyle = RecipeVisualStyle.default): Future[String] = {
    for {
      getRecipeResponse <- processIndexActor.ask(GetCompiledRecipe(processId))(config.defaultInquireTimeout)
      processState <- getProcessState(processId)
      response <- getRecipeResponse match {
        case RecipeFound(compiledRecipe, _) =>
          Future.successful(RecipeVisualizer.visualizeRecipe(
            compiledRecipe,
            style,
            eventNames = processState.eventNames.toSet,
            ingredientNames = processState.ingredients.keySet))
        case ProcessDeleted(_) =>
          Future.failed(new ProcessDeletedException(s"Process $processId is deleted"))
        case Uninitialized(_) =>
          Future.failed(new NoSuchProcessException(s"Process $processId is not found"))
      }
    } yield response
  }

  private def doRegisterEventListener(listenerFunction: (String, RuntimeEvent) => Unit, processFilter: String => Boolean): Future[Unit] = {
    Future.successful(createBakerEventListenerActor {
      case EventReceived(_, recipeName, _, processId, _, event) if processFilter(recipeName) =>
        listenerFunction.apply(processId, event)
      case InteractionCompleted(_, _, recipeName, _, processId, _, Some(event)) if processFilter(recipeName) =>
        listenerFunction.apply(processId, event)
      case InteractionFailed(_, _, recipeName, _, processId, _, _, _, ExceptionStrategyOutcome.Continue(eventName)) if processFilter(recipeName) =>
        listenerFunction.apply(processId, RuntimeEvent(eventName, Map.empty))
      case _ => ()
    })
  }

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(recipeName: String, listenerFunction: (String, RuntimeEvent) => Unit): Future[Unit] =
    doRegisterEventListener(listenerFunction, _ == recipeName)

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  //  @deprecated("Use event bus instead", "1.4.0")
  override def registerEventListener(listenerFunction: (String, RuntimeEvent) => Unit): Future[Unit] =
    doRegisterEventListener(listenerFunction, _ => true)

  /**
    * Registers a listener function that listens to all BakerEvents
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    *
    * @param listener
    * @return
    */
  override def registerBakerEventListener(listenerFunction: BakerEvent => Unit): Future[Unit] = {
    Future.successful(createBakerEventListenerActor(listenerFunction))
  }

  private def createBakerEventListenerActor(listenerFunction: BakerEvent => Unit): Unit = {
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

  /**
    * Adds an interaction implementation to baker.
    *
    * This is assumed to be a an object with a method named 'apply' defined on it.
    *
    * @param implementation The implementation object
    */
  override def addImplementation(implementation: InteractionImplementation): Future[Unit] =
    Future.successful(config.interactionManager.addImplementation(implementation))

  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  override def addImplementations(implementations: Seq[InteractionImplementation]): Future[Unit] =
    Future.successful(implementations.foreach(addImplementation))

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown(): Future[Unit] =
    Future.successful(GracefulShutdown.gracefulShutdownActorSystem(system, config.defaultShutdownTimeout))
}
