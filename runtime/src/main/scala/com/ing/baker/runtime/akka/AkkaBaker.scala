package com.ing.baker.runtime.akka

import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.actor.{Actor, ActorRef, ActorSystem, Props}
import akka.pattern.ask
import akka.pattern.FutureRef
import akka.persistence.query.PersistenceQuery
import akka.persistence.query.scaladsl._
import akka.stream.ActorMaterializer
import akka.stream.scaladsl.{Flow, Source}
import akka.util.Timeout
import com.ing.baker.il._
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.akka.actor._
import com.ing.baker.runtime.akka.actor.process_index.ProcessEventReceiver
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol.{Initialized, InstanceState, Uninitialized}
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.akka.actor.serialization.Encryption
import com.ing.baker.runtime.akka.actor.serialization.Encryption.NoEncryption
import com.ing.baker.runtime.common._
import com.ing.baker.runtime.{akka, common}
import com.ing.baker.runtime.akka.events.{BakerEvent, EventReceived, InteractionCompleted, InteractionFailed}
import com.ing.baker.runtime.akka.internal.{InteractionManager, MethodInteractionImplementation}
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.types.Value
import com.typesafe.config.{Config, ConfigFactory}
import net.ceedubs.ficus.Ficus._
import org.slf4j.LoggerFactory

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.concurrent.duration.FiniteDuration
import scala.language.postfixOps
import scala.util.Try


/**
  * The Baker is the component of the Baker library that runs one or multiples recipes.
  * For each recipe a new instance can be baked, sensory events can be send and state can be inquired upon
  */
class AkkaBaker(config: Config)(implicit val actorSystem: ActorSystem) extends Baker {

  private val log = LoggerFactory.getLogger(classOf[AkkaBaker])

  if (!config.getAs[Boolean]("baker.config-file-included").getOrElse(false))
    throw new IllegalStateException("You must 'include baker.conf' in your application.conf")

  private val interactionManager: InteractionManager = new InteractionManager()

  val defaultBakeTimeout: FiniteDuration = config.as[FiniteDuration]("baker.bake-timeout")
  val defaultProcessEventTimeout: FiniteDuration = config.as[FiniteDuration]("baker.process-event-timeout")
  val defaultInquireTimeout: FiniteDuration = config.as[FiniteDuration]("baker.process-inquire-timeout")
  val defaultShutdownTimeout: FiniteDuration = config.as[FiniteDuration]("baker.shutdown-timeout")
  val defaultAddRecipeTimeout: FiniteDuration = config.as[FiniteDuration]("baker.add-recipe-timeout")

  private val readJournalIdentifier = config.as[String]("baker.actor.read-journal-plugin")
  private implicit val materializer: ActorMaterializer = ActorMaterializer()

  private val readJournal = PersistenceQuery(actorSystem)
    .readJournalFor[CurrentEventsByPersistenceIdQuery with PersistenceIdsQuery with CurrentPersistenceIdsQuery](readJournalIdentifier)

  private val configuredEncryption: Encryption = {
    val encryptionEnabled = config.getAs[Boolean]("baker.encryption.enabled").getOrElse(false)
    if (encryptionEnabled) {
      new Encryption.AESEncryption(config.as[String]("baker.encryption.secret"))
    } else {
      NoEncryption
    }
  }

  private val bakerActorProvider =
    config.as[Option[String]]("baker.actor.provider") match {
      case None | Some("local") => new LocalBakerActorProvider(config, configuredEncryption)
      case Some("cluster-sharded") => new ClusterBakerActorProvider(config, configuredEncryption)
      case Some(other) => throw new IllegalArgumentException(s"Unsupported actor provider: $other")
    }

  val recipeManager: ActorRef = bakerActorProvider.createRecipeManagerActor()

  val processIndexActor: ActorRef =
    bakerActorProvider.createProcessIndexActor(interactionManager, recipeManager)

  override type Result = SensoryEventResult

  override type Moments = SensoryEventMoments

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
      return Future.failed(new BakerException(implementationErrors.mkString(", ")))

    if (compiledRecipe.validationErrors.nonEmpty)
      return Future.failed(new RecipeValidationException(compiledRecipe.validationErrors.mkString(", ")))

    recipeManager.ask(AddRecipe(compiledRecipe))(defaultAddRecipeTimeout) flatMap {
      case AddRecipeResponse(recipeId) => Future.successful(recipeId)
      case _ => Future.failed(new BakerException(s"Unexpected error happened when adding recipe"))
    }
  }

  private def getImplementationErrors(compiledRecipe: CompiledRecipe): Set[String] = {
    compiledRecipe.interactionTransitions.filterNot(interactionManager.getImplementation(_).isDefined)
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
    recipeManager.ask(GetRecipe(recipeId))(defaultInquireTimeout).flatMap {
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
    recipeManager.ask(GetAllRecipes)(defaultInquireTimeout)
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
    processIndexActor.ask(CreateProcess(recipeId, processId))(defaultBakeTimeout).flatMap {
      case _: Initialized =>
        Future.successful(())
      case CreateProcessRejection.ProcessAlreadyExists(_) =>
        Future.failed(new IllegalArgumentException(s"Process with id '$processId' already exists."))
      case CreateProcessRejection.NoRecipeFound(_, _) =>
        Future.failed(new IllegalArgumentException(s"Recipe with id '$recipeId' does not exist."))
      case msg@_ =>
        Future.failed(new BakerException(s"Unexpected message of type: ${msg.getClass}"))
    }
  }

  def fireSensoryEventReceived(processId: String, event: Any): Future[SensoryEventStatus] =
    processIndexActor.ask(ProcessEvent(
      processId = processId,
      event = RuntimeEvent.extractEvent(event),
      correlationId = None,
      timeout = defaultProcessEventTimeout,
      reaction = FireSensoryEventReaction.NotifyWhenReceived
    ))(defaultProcessEventTimeout).flatMap {
      case rejection: FireSensoryEventRejection =>
        Future.failed(new BakerException(rejection.asReason.toString))
      case status: SensoryEventStatus =>
        Future.successful(status)
    }

  def fireSensoryEventCompleted(processId: String, event: Any): Future[SensoryEventResult] =
    processIndexActor.ask(ProcessEvent(
      processId = processId,
      event = RuntimeEvent.extractEvent(event),
      correlationId = None,
      timeout = defaultProcessEventTimeout,
      reaction = FireSensoryEventReaction.NotifyWhenCompleted(waitForRetries = true)
    ))(defaultProcessEventTimeout).flatMap {
      case rejection: FireSensoryEventRejection =>
        Future.failed(new BakerException(rejection.asReason.toString))
      case result: SensoryEventResult =>
        Future.successful(result)
    }

  def fireSensoryEvent(processId: String, event: Any): SensoryEventMoments = {
    val futureRef = FutureRef(defaultProcessEventTimeout)
    val futureReceived =
      processIndexActor.ask(ProcessEvent(
        processId = processId,
        event = RuntimeEvent.extractEvent(event),
        correlationId = None,
        timeout = defaultProcessEventTimeout,
        reaction = FireSensoryEventReaction.NotifyBoth(waitForRetries = true, completeReceiver = futureRef.ref)
      ))(defaultProcessEventTimeout).flatMap {
        case rejection: FireSensoryEventRejection =>
          Future.failed(new BakerException(rejection.asReason.toString))
        case status: SensoryEventStatus =>
          Future.successful(status)
      }
    val futureCompleted =
      futureRef.future.flatMap {
        case rejection: FireSensoryEventRejection =>
          Future.failed(new BakerException(rejection.asReason.toString))
        case result: SensoryEventResult =>
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
    processIndexActor.ask(RetryBlockedInteraction(processId, interactionName))(defaultProcessEventTimeout).map(_ => ())
  }

  /**
    * Resolves a blocked interaction by specifying it's output.
    *
    * !!! You should provide an event of the original interaction. Event / ingredient renames are done by Baker.
    *
    * @return
    */
  override def resolveInteraction(processId: String, interactionName: String, event: Any): Future[Unit] = {
    processIndexActor.ask(ResolveBlockedInteraction(processId, interactionName, RuntimeEvent.extractEvent(event)))(defaultProcessEventTimeout).map(_ => ())
  }

  /**
    * Stops the retrying of an interaction.
    *
    * @return
    */
  override def stopRetryingInteraction(processId: String, interactionName: String): Future[Unit] = {
    processIndexActor.ask(StopRetryingInteraction(processId, interactionName))(defaultProcessEventTimeout).map(_ => ())
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
    Future.successful(bakerActorProvider
      .getIndex(processIndexActor)(actorSystem, defaultInquireTimeout)
      .map(p => ProcessMetadata(p.recipeId, p.processId, p.createdDateTime)).toSet)
  }

  /**
    * Returns the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  override def getProcessState(processId: String): Future[ProcessState] =
    processIndexActor
      .ask(GetProcessState(processId))(Timeout.durationToTimeout(defaultInquireTimeout))
      .flatMap {
        case instance: InstanceState => Future.successful(instance.state.asInstanceOf[ProcessState])
        case ProcessRejection.NoSuchProcess(id) => Future.failed(new NoSuchProcessException(s"No such process with: $id"))
        case ProcessRejection.ProcessDeleted(id) => Future.failed(new ProcessDeletedException(s"Process $id is deleted"))
        case msg => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
      }

  /**
    * Returns all provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return The provided ingredients.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("If the process is already deleted")
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
  override def getVisualState(processId: String): Future[String] = {
    for {
      getRecipeResponse <- processIndexActor.ask(GetCompiledRecipe(processId))(defaultInquireTimeout)
      processState <- getProcessState(processId)
      response <- getRecipeResponse match {
        case RecipeFound(compiledRecipe, _) =>
          Future.successful(RecipeVisualizer.visualizeRecipe(
            compiledRecipe,
            config,
            eventNames = processState.eventNames.toSet,
            ingredientNames = processState.ingredients.keySet))
        case ProcessRejection.ProcessDeleted(_) =>
          Future.failed(new ProcessDeletedException(s"Process $processId is deleted"))
        case Uninitialized(_) =>
          Future.failed(new NoSuchProcessException(s"Process $processId is not found"))
      }
    } yield response
  }

  private def doRegisterEventListener(listener: EventListener, processFilter: String => Boolean): Future[Unit] = {

    registerEventListenerPF {

      case EventReceived(_, recipeName, _, processId, _, event) if processFilter(recipeName) =>
        listener.processEvent(processId, event)
      case InteractionCompleted(_, _, recipeName, _, processId, _, Some(event)) if processFilter(recipeName) =>
        listener.processEvent(processId, event)
      case InteractionFailed(_, _, recipeName, _, processId, _, _, _, ExceptionStrategyOutcome.Continue(eventName)) if processFilter(recipeName) =>
        listener.processEvent(processId, RuntimeEvent(eventName, Seq.empty))
    }
  }

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  override def registerEventListener(recipeName: String, listener: EventListener): Future[Unit] =
    doRegisterEventListener(listener, _ == recipeName)

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  //  @deprecated("Use event bus instead", "1.4.0")
  override def registerEventListener(listener: EventListener): Future[Unit] =
    doRegisterEventListener(listener, _ => true)

  /**
    * This registers a listener function.
    *
    * @param pf A partial function that receives the events.
    * @return
    */
  def registerEventListenerPF(pf: PartialFunction[BakerEvent, Unit]): Future[Unit] = {

    val listenerActor = actorSystem.actorOf(Props(new Actor() {
      override def receive: Receive = {
        case event: BakerEvent => Try {
          pf.applyOrElse[BakerEvent, Unit](event, _ => ())
        }.failed.foreach { e =>
          log.warn(s"Listener function threw exception for event: $event", e)
        }
      }
    }))

    actorSystem.eventStream.subscribe(listenerActor, classOf[BakerEvent])
    Future.successful(())
  }

  /**
    * Adds an interaction implementation to baker.
    *
    * This is assumed to be a an object with a method named 'apply' defined on it.
    *
    * @param implementation The implementation object
    */
  override def addImplementation(implementation: AnyRef): Future[Unit] =
    Future.successful(interactionManager.addImplementation(MethodInteractionImplementation(implementation)))

  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  override def addImplementations(implementations: Seq[AnyRef]): Future[Unit] =
    Future.successful(implementations.foreach(addImplementation))

  /**
    * Adds an interaction implementation to baker.
    *
    * @param implementation An InteractionImplementation instance
    */
  override def addImplementation(implementation: InteractionImplementation): Future[Unit] =
    Future.successful(interactionManager.addImplementation(implementation))

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  override def gracefulShutdown(): Future[Unit] =
    Future.successful(GracefulShutdown.gracefulShutdownActorSystem(actorSystem, defaultShutdownTimeout))
}
