package com.ing.baker.runtime.core

import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.actor.{Actor, ActorRef, ActorSystem, Props}
import akka.cluster.Cluster
import akka.pattern.ask
import akka.persistence.query.PersistenceQuery
import akka.persistence.query.scaladsl._
import akka.stream.ActorMaterializer
import akka.stream.scaladsl.{Sink, Source}
import akka.util.Timeout
import com.ing.baker.il._
import com.ing.baker.il.petrinet._
import com.ing.baker.petrinet.runtime.EventSourcing.{TransitionFailedEvent, TransitionFiredEvent}
import com.ing.baker.petrinet.runtime.ExceptionStrategy.Continue
import com.ing.baker.runtime.actor._
import com.ing.baker.runtime.actor.process_index.ProcessEventActor
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceEvent
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol.{Initialized, InstanceState, Uninitialized}
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.actor.serialization.Encryption
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import com.ing.baker.runtime.core.Baker._
import com.ing.baker.runtime.core.events.{BakerEvent, RecipeAdded}
import com.ing.baker.runtime.core.interations.{InteractionImplementation, InteractionManager, MethodInteractionImplementation}
import com.ing.baker.runtime.event_extractors.{CompositeEventExtractor, EventExtractor}
import com.ing.baker.runtime.petrinet.RecipeRuntime
import com.ing.baker.types.Value
import net.ceedubs.ficus.Ficus._
import org.slf4j.LoggerFactory

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{Await, Future}
import scala.language.postfixOps
import scala.util.{Failure, Success, Try}

object Baker {

  val eventExtractor: EventExtractor = new CompositeEventExtractor()

  def toImplementations(seq: Seq[(String, Seq[Any] => Any)]): InteractionTransition[_] => (Seq[Any] => Any) = {
    val map = seq.toMap
    i => map(i.interactionName)
  }

  /**
    * Translates a petri net TransitionFiredEvent to an optional RuntimeEvent
    */
  def toRuntimeEvent[P[_], T[_], E](event: TransitionFiredEvent[P, T, E]): Option[RuntimeEvent] = {
    val t = event.transition.asInstanceOf[Transition[_]]
    if ((t.isSensoryEvent || t.isInteraction) && event.output.isInstanceOf[RuntimeEvent])
      Some(event.output.asInstanceOf[RuntimeEvent])
    else
      None
  }

  private def checkIfValidImplementationsProvided(interactionManager: InteractionManager, actions: Set[InteractionTransition[_]]): Set[String] = {
    actions.filterNot(interactionManager.getImplementation(_).isDefined)
      .map(s => s"No implementation provided for interaction: ${s.originalInteractionName}")
  }
}

/**
  * The Baker is the component of the Baker library that runs one or multiples recipes.
  * For each recipe a new instance can be baked, sensory events can be send and state can be inquired upon
  */
class Baker()(implicit val actorSystem: ActorSystem) {

  private val interactionManager: InteractionManager = new InteractionManager()
  private val config = actorSystem.settings.config
  private val defaultBakeTimeout = config.as[FiniteDuration]("baker.bake-timeout")
  private val defaultProcessEventTimeout = config.as[FiniteDuration]("baker.process-event-timeout")
  private val defaultInquireTimeout = config.as[FiniteDuration]("baker.process-inquire-timeout")
  private val defaultShutdownTimeout = config.as[FiniteDuration]("baker.shutdown-timeout")
  private val readJournalIdentifier = config.as[String]("baker.actor.read-journal-plugin")
  private val log = LoggerFactory.getLogger(classOf[Baker])

  private implicit val materializer: ActorMaterializer = ActorMaterializer()

  if (!config.as[Option[Boolean]]("baker.config-file-included").getOrElse(false))
    throw new IllegalStateException("You must 'include baker.conf' in your application.conf")

  private val readJournal = PersistenceQuery(actorSystem)
    .readJournalFor[CurrentEventsByPersistenceIdQuery with PersistenceIdsQuery with CurrentPersistenceIdsQuery](readJournalIdentifier)

  private val configuredEncryption: Encryption = {
    val encryptionEnabled = config.getAs[Boolean]("baker.encryption.enabled").getOrElse(false)
    if (encryptionEnabled) {
      new Encryption.AESEncryption(config.getString("baker.encryption.secret"))
    } else {
      NoEncryption
    }
  }

  private val bakerActorProvider =
    config.as[Option[String]]("baker.actor.provider") match {
      case None | Some("local")    => new LocalBakerActorProvider(config, configuredEncryption)
      case Some("cluster-sharded") => new ClusterBakerActorProvider(config, configuredEncryption)
      case Some(other)             => throw new IllegalArgumentException(s"Unsupported actor provider: $other")
    }

  val recipeManager: ActorRef = bakerActorProvider.createRecipeManagerActor()

  val processIndexActor: ActorRef =
    bakerActorProvider.createProcessIndexActor(interactionManager, recipeManager)

  /**
    * Adds a recipe to baker and returns a recipeId for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the same recipeId
    *
    * @param compiledRecipe The compiled recipe.
    * @return A recipeId
    */
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def addRecipe(compiledRecipe: CompiledRecipe, timeout: FiniteDuration = defaultBakeTimeout): String = {

    val implementationErrors = checkIfValidImplementationsProvided(interactionManager, compiledRecipe.interactionTransitions)
    if (implementationErrors.nonEmpty)
      throw new BakerException(implementationErrors.mkString(", "))

    if (compiledRecipe.validationErrors.nonEmpty)
      throw new RecipeValidationException(compiledRecipe.validationErrors.mkString(", "))

    val futureResult = recipeManager.ask(AddRecipe(compiledRecipe))(timeout)
    Await.result(futureResult, timeout) match {
      case AddRecipeResponse(recipeId) => recipeId
      case _ => throw new BakerException(s"Unexpected error happened when adding recipe")
    }
  }

  /**
    * Returns the recipe for the given RecipeId
    *
    * @param recipeId
    * @return
    */
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getRecipe(recipeId: String, timeout: FiniteDuration = defaultInquireTimeout): CompiledRecipe = {

    // here we ask the RecipeManager actor to return us the recipe for the given id
    val futureResult = recipeManager.ask(GetRecipe(recipeId))(timeout)
    Await.result(futureResult, timeout) match {
      case RecipeFound(compiledRecipe) => compiledRecipe
      case NoRecipeFound(_) => throw new IllegalArgumentException(s"No recipe found for recipe with id: $recipeId")
    }
  }

  /**
    * Returns all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getAllRecipes(timeout: FiniteDuration = defaultInquireTimeout): Map[String, CompiledRecipe] =
    Await.result(getAllRecipesAsync(timeout), timeout)

  /**
    * Returns a future of all recipes added to this baker instance.
    *
    * @return All recipes in the form of map of recipeId -> CompiledRecipe
    */
  def getAllRecipesAsync(timeout: FiniteDuration = defaultInquireTimeout): Future[Map[String, CompiledRecipe]] =
    recipeManager.ask(GetAllRecipes)(timeout)
      .mapTo[AllRecipes]
      .map(_.compiledRecipes)

  /**
    * Creates a process instance for the given recipeId with the given processId as identifier
    *
    * @param recipeId  The recipeId for the recipe to bake
    * @param processId The identifier for the newly baked process
    * @param timeout
    * @return
    */
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def bake(recipeId: String, processId: String, timeout: FiniteDuration = defaultBakeTimeout): ProcessState =
    Await.result(bakeAsync(recipeId, processId), timeout)

  /**
    * Asynchronously creates a process instance for the given recipeId with the given processId as identifier
    *
    * @param recipeId  The recipeId for the recipe to bake
    * @param processId The identifier for the newly baked process
    * @param timeout
    * @return
    */
  def bakeAsync(recipeId: String, processId: String, timeout: FiniteDuration = defaultBakeTimeout): Future[ProcessState] = {

    implicit val askTimeout = Timeout(timeout)

    val initializeFuture = processIndexActor ? CreateProcess(recipeId, processId)

    val eventualState: Future[ProcessState] = initializeFuture.map {
      case msg: Initialized             => msg.state.asInstanceOf[ProcessState]
      case ProcessAlreadyInitialized(_) => throw new IllegalArgumentException(s"Process with id '$processId' already exists.")
      case NoRecipeFound(_)             => throw new IllegalArgumentException(s"Recipe with id '$recipeId' does not exist.")
      case msg @ _                      => throw new BakerException(s"Unexpected message of type: ${msg.getClass}")
    }

    eventualState
  }

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * @param processId The process identifier
    * @param event     The event object
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def processEvent(processId: String, event: Any, correlationId: Option[String] = None, timeout: FiniteDuration = defaultProcessEventTimeout): SensoryEventStatus = {
    processEventAsync(processId, event, correlationId, timeout).confirmCompleted(timeout)
  }

  /**
    * Notifies Baker that an event has happened.
    *
    * If nothing is done with the BakerResponse there is NO guarantee that the event is received by the process instance.
    */
  def processEventAsync(processId: String, event: Any, correlationId: Option[String] = None, timeout: FiniteDuration = defaultProcessEventTimeout): BakerResponse = {

    // transforms the given object into a RuntimeEvent instance
    val runtimeEvent: RuntimeEvent = event match {
      case runtimeEvent: RuntimeEvent => runtimeEvent
      case _                          => Baker.eventExtractor.extractEvent(event)
    }

    implicit val implicitTimeout = timeout

    // sends the ProcessEvent command to the actor and retrieves a Source (stream) of responses.
    val source: Source[Any, NotUsed] = ProcessEventActor.processEvent(
      processIndexActor, ProcessEvent(processId, runtimeEvent, correlationId), waitForRetries = true)

    new BakerResponse(processId, source)
  }

  /**
    * Synchronously returns all event names that occurred for a process.
    */
  def eventNames(processId: String, timeout: FiniteDuration = defaultInquireTimeout): List[String] =
    getProcessState(processId, timeout).eventNames

  private def getEventsForRecipe(processId: String, compiledRecipe: CompiledRecipe): Source[(RuntimeEvent, Long), NotUsed] = {
    ProcessQuery
      .eventsForInstance[Place, Transition, ProcessState, RuntimeEvent](compiledRecipe.name, processId, compiledRecipe.petriNet, configuredEncryption, readJournal, RecipeRuntime.eventSourceFn)
      .collect {
        case (_, TransitionFiredEvent(_, _, _, _, time, _, _, runtimeEvent: RuntimeEvent))
          if runtimeEvent != null && compiledRecipe.allEvents.exists(e => e.name equals runtimeEvent.name) => (runtimeEvent, time)
      }
  }

  /**
    * Returns a stream of all events with their timestamps for a process.
    *
    * @param processId The process identifier.
    * @return The source of events.
    */
  def eventsWithTimestampAsync(processId: String): Source[(RuntimeEvent, Long), NotUsed] = {

    val futureResult = processIndexActor.ask(GetCompiledRecipe(processId))(defaultInquireTimeout)

    Await.result(futureResult, defaultInquireTimeout) match {
      case RecipeFound(compiledRecipe) => getEventsForRecipe(processId, compiledRecipe)
      case ProcessDeleted(_)           => throw new ProcessDeletedException(s"Process $processId is deleted")
      case ProcessUninitialized(_)     => throw new NoSuchProcessException(s"No process found for $processId")
      case _                           => throw new BakerException("Unknown response received")
    }
  }

  /**
    * Returns a stream of all events for a process.
    *
    * @param processId The process identifier.
    * @return A sequence of events with their timestamps.
    */
  def eventsAsync(processId: String): Source[RuntimeEvent, NotUsed] =
    eventsWithTimestampAsync(processId).map { case (event, _) => event }

  /**
    * Synchronously returns a sequence of all events for a process.
    *
    * @param processId The process identifier.
    * @param timeout How long to wait to retrieve the events.
    */
  def events(processId: String, timeout: FiniteDuration = defaultInquireTimeout): Seq[RuntimeEvent] =
    eventsWithTimestamp(processId, timeout).map { case (event, _) => event }

  /**
    * Synchronously returns a sequence of all events with their timestamps for a process.
    *
    * @param processId The process identifier.
    * @param timeout How long to wait to retrieve the events.
    * @return A sequence of events with their timestamps.
    */
  def eventsWithTimestamp(processId: String, timeout: FiniteDuration = defaultInquireTimeout): Seq[(RuntimeEvent, Long)] = {
    val futureEventSeq = eventsWithTimestampAsync(processId).runWith(Sink.seq)
    Await.result(futureEventSeq, timeout)
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
  def getIndex(timeout: FiniteDuration = defaultInquireTimeout): Set[ProcessMetadata] = {
    bakerActorProvider
      .getIndex(processIndexActor)(actorSystem, timeout)
      .map(p => ProcessMetadata(p.recipeId, p.processId, p.createdDateTime))
  }

  /**
    * Returns the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getProcessState(processId: String, timeout: FiniteDuration = defaultInquireTimeout): ProcessState =
    Await.result(getProcessStateAsync(processId), timeout)

  /**
    * returns a future with the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getProcessStateAsync(processId: String, timeout: FiniteDuration = defaultInquireTimeout): Future[ProcessState] = {
    processIndexActor
      .ask(GetProcessState(processId))(Timeout.durationToTimeout(timeout))
      .flatMap {
        case instane: InstanceState   => Future.successful(instane.state.asInstanceOf[ProcessState])
        case Uninitialized(id)        => Future.failed(new NoSuchProcessException(s"No such process with: $id"))
        case ProcessUninitialized(id) => Future.failed(new NoSuchProcessException(s"No such process with: $id"))
        case ProcessDeleted(id)       => Future.failed(new ProcessDeletedException(s"Process $id is deleted"))
        case msg                      => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
      }
  }

  /**
    * Returns all provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return The provided ingredients.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getIngredients(processId: String, timeout: FiniteDuration = defaultInquireTimeout): Map[String, Value] =
    getProcessState(processId).ingredients

  /**
    * Returns a future of all the provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return A future of the provided ingredients.
    */
  def getIngredientsAsync(processId: String, timeout: FiniteDuration = defaultInquireTimeout): Future[Map[String, Value]] = {
    getProcessStateAsync(processId).map(_.ingredients)
  }

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param processId The process identifier.
    * @param timeout   How long to wait to retrieve the process state.
    * @return A visual (.dot) representation of the process state.
    */
  @throws[ProcessDeletedException]("If the process is already deleted")
  @throws[NoSuchProcessException]("If the process is not found")
  def getVisualState(processId: String, timeout: FiniteDuration = defaultInquireTimeout): String = {
    val futureResult = processIndexActor.ask(GetCompiledRecipe(processId))(timeout)
    Await.result(futureResult, timeout) match {
      case RecipeFound(compiledRecipe) =>
        RecipeVisualizer.visualiseCompiledRecipe(
          compiledRecipe,
          eventNames = events(processId).map(_.name).toSet,
          ingredientNames = getIngredients(processId).keySet)
      case ProcessDeleted(_) => throw new ProcessDeletedException(s"Process $processId is deleted")
      case Uninitialized(_)  => throw new NoSuchProcessException(s"Process $processId is not found")
    }
  }

  private def doRegisterEventListener(listener: EventListener, processFilter: String => Boolean): Boolean = {
    val subscriber = actorSystem.actorOf(Props(new Actor() {
      override def receive: Receive = {
        case ProcessInstanceEvent(processType, processId, event: TransitionFiredEvent[_, _, _]) if processFilter(processType) =>
          toRuntimeEvent(event).foreach(e => listener.processEvent(processId, e))
        case ProcessInstanceEvent(processType, processId, event: TransitionFailedEvent[_, _, _]) if processFilter(processType) =>
          event.exceptionStrategy match {
            case Continue(_, event: RuntimeEvent) =>
              listener.processEvent(processId, event)
            case _ =>
          }
        case _: ProcessInstanceEvent => // purposely ignored in order to not have unnecessary unhandled messages logged
      }
    }))
    actorSystem.eventStream.subscribe(subscriber.actorRef, classOf[ProcessInstanceEvent])
  }

  /**
    * Registers a listener to all runtime events for recipes with the given name run in this baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  def registerEventListener(recipeName: String, listener: EventListener): Boolean =
    doRegisterEventListener(listener, _ == recipeName)

  /**
    * Registers a listener to all runtime events for all recipes that run in this Baker instance.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
//  @deprecated("Use event bus instead", "1.4.0")
  def registerEventListener(listener: EventListener): Boolean =
    doRegisterEventListener(listener, _ => true)

  /**
    * This registers a listener function.
    *
    * @param pf A partial function that receives the events.
    * @return
    */
  def registerEventListenerPF(pf: PartialFunction[BakerEvent, Unit]): Boolean = {

    val listenerActor = actorSystem.actorOf(Props(new Actor() {
      override def receive = {
        case event: BakerEvent => Try { pf.applyOrElse[BakerEvent, Unit](event, _ => ()) }.failed.foreach { e =>
          log.warn(s"Listener function threw exception for event: $event", e)
        }
      }
    }))

    actorSystem.eventStream.subscribe(listenerActor, classOf[BakerEvent])
  }

  /**
    * Adds an interaction implementation to baker.
    *
    * This is assumed to be a an object with a method named 'apply' defined on it.
    *
    * @param implementation The implementation object
    */
  def addImplementation(implementation: AnyRef): Unit =
    MethodInteractionImplementation.anyRefToInteractionImplementations(implementation).foreach(interactionManager.addImplementation)

  /**
    * Adds a sequence of interaction implementation to baker.
    *
    * @param implementations The implementation object
    */
  def addImplementation(implementations: Seq[AnyRef]): Unit =
    implementations.foreach(addImplementation)

  /**
    * Adds an interaction implementation to baker.
    *
    * @param implementation An InteractionImplementation instance
    */
  def addImplementation(implementation: InteractionImplementation): Unit =
    interactionManager.addImplementation(implementation)

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  def shutdown(timeout: FiniteDuration = defaultShutdownTimeout): Unit = {
    Try {
      Cluster.get(actorSystem)
    } match {
      case Success(cluster) if cluster.state.members.exists(_.uniqueAddress == cluster.selfUniqueAddress) =>
        cluster.registerOnMemberRemoved {
          actorSystem.terminate()
        }
        implicit val akkaTimeout = Timeout(timeout)
        Util.handOverShardsAndLeaveCluster(Seq("ProcessIndexActor"))
      case Success(_) =>
        log.debug("ActorSystem not a member of cluster")
        actorSystem.terminate()
      case Failure(exception) =>
        log.debug("Cluster not available for actor system", exception)
        actorSystem.terminate()
    }
  }
}
