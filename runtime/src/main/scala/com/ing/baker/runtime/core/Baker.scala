package com.ing.baker.runtime.core

import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.actor.{Actor, ActorRef, ActorSystem, Address, AddressFromURIString, Props}
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
import com.ing.baker.runtime.actor.process_index.ProcessApi
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceEvent
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol.{Initialized, InstanceState, Uninitialized}
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.actor.serialization.Encryption
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import com.ing.baker.runtime.core.Baker._
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
  def toRuntimeEvent[P[_], T[_, _], E](event: TransitionFiredEvent[P, T, E]): Option[RuntimeEvent] = {
    val t = event.transition.asInstanceOf[Transition[_, _]]
    if ((t.isSensoryEvent || t.isInteraction) && event.output.isInstanceOf[RuntimeEvent])
      Some(event.output.asInstanceOf[RuntimeEvent])
    else
      None
  }

  private def checkIfValidImplementationsProvided(interactionManager: InteractionManager, actions: Set[InteractionTransition[_]]): Set[String] = {
    actions.filterNot(interactionManager.hasCompatibleImplementation)
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
  private val journalInitializeTimeout = config.as[FiniteDuration]("baker.journal-initialize-timeout")
  private val readJournalIdentifier = config.as[String]("baker.actor.read-journal-plugin")
  private val log = LoggerFactory.getLogger(classOf[Baker])

  implicit val materializer: ActorMaterializer = ActorMaterializer()

  private val readJournal = PersistenceQuery(actorSystem)
    .readJournalFor[CurrentEventsByPersistenceIdQuery with PersistenceIdsQuery with CurrentPersistenceIdsQuery](readJournalIdentifier)

  private def initializeCluster() = {

    val seedNodes: List[Address] = config.as[Option[List[String]]]("baker.cluster.seed-nodes") match {
      case Some(_seedNodes) if _seedNodes.nonEmpty =>
        _seedNodes map AddressFromURIString.parse
      case None =>
        throw new BakerException("Baker cluster configuration without baker.cluster.seed-nodes")
    }

    /**
      * Join cluster after waiting for the persistenceInit actor, otherwise terminate here.
      */
    Await.result(Util.persistenceInit(journalInitializeTimeout), journalInitializeTimeout)

    // join the cluster
    log.info("PersistenceInit actor started successfully, joining cluster seed nodes {}", seedNodes)
    Cluster.get(actorSystem).joinSeedNodes(seedNodes)
  }

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
      case None | Some("local") =>
        new LocalBakerActorProvider(config)
      case Some("cluster-sharded") =>
        initializeCluster()
        new ClusterBakerActorProvider(config, configuredEncryption)
      case Some(other) =>
        throw new IllegalArgumentException(s"Unsupported actor provider: $other")
    }

  val recipeManager: ActorRef = bakerActorProvider.createRecipeManagerActor()

  val processIndexActor: ActorRef =
    bakerActorProvider.createProcessIndexActor(interactionManager, recipeManager)

  private val petriNetApi = new ProcessApi(processIndexActor)

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
  def getAllRecipes(timeout: FiniteDuration = defaultInquireTimeout): Map[String, CompiledRecipe] = {
    val futureResult = recipeManager.ask(GetAllRecipes)(timeout).mapTo[AllRecipes]
    Await.result(futureResult, timeout).compiledRecipes
  }

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

    val msg = CreateProcess(recipeId, processId)
    val initializeFuture = processIndexActor ? msg

    val eventualState: Future[ProcessState] = initializeFuture.map {
      case msg: Initialized => msg.state.asInstanceOf[ProcessState]
      case ProcessAlreadyInitialized(_) =>
        throw new IllegalArgumentException(s"Process with id '$processId' already exists.")
      case NoRecipeFound(_) => throw new IllegalArgumentException(s"Recipe with id '$recipeId' does ont exist.")
      case msg@_ => throw new BakerException(s"Unexpected message: $msg")
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
    processEventAsync(processId, event, correlationId, timeout).confirmCompleted()
  }

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * This call is fire and forget: If  nothing is done
    * with the response object there is NO guarantee that the event is received by the process instance.
    */
  def processEventAsync(processId: String, event: Any, correlationId: Option[String] = None, timeout: FiniteDuration = defaultProcessEventTimeout): BakerResponse = {

    val runtimeEvent: RuntimeEvent = event match {
      case runtimeEvent: RuntimeEvent => runtimeEvent
      case _ => Baker.eventExtractor.extractEvent(event)
    }

    val source = petriNetApi.askAndCollectAll(ProcessEvent(processId, runtimeEvent, correlationId), waitForRetries = true)(timeout)
    new BakerResponse(processId, source)
  }

  /**
    * Synchronously returns all events that occurred for a process.
    */
  def events(processId: String, timeout: FiniteDuration = defaultInquireTimeout): Seq[RuntimeEvent] = {
    val futureEventSeq = eventsAsync(processId).runWith(Sink.seq)
    Await.result(futureEventSeq, timeout)
  }

  /**
    * Synchronously returns all event names that occurred for a process.
    */
  def eventNames(processId: String, timeout: FiniteDuration = defaultInquireTimeout): List[String] =
    getProcessState(processId, timeout).eventNames

  /**
    * Returns a Source of baker events for a process.
    *
    * @param processId The process identifier.
    * @return The source of events.
    */
  def eventsAsync(processId: String): Source[RuntimeEvent, NotUsed] = {

    def getEventsForRecipe(compiledRecipe: CompiledRecipe): Source[RuntimeEvent, NotUsed] = {
      ProcessQuery
        .eventsForInstance[Place, Transition, ProcessState, RuntimeEvent](compiledRecipe.name, processId.toString, compiledRecipe.petriNet, configuredEncryption, readJournal, RecipeRuntime.eventSourceFn)
        .collect {
          case (_, TransitionFiredEvent(_, _, _, _, _, _, _, runtimeEvent: RuntimeEvent))
            if runtimeEvent != null && compiledRecipe.allEvents.exists(e => e.name equals runtimeEvent.name) => runtimeEvent
        }
    }

    val futureResult = processIndexActor.ask(GetCompiledRecipe(processId))(defaultInquireTimeout)
    Await.result(futureResult, defaultInquireTimeout) match {
      case RecipeFound(compiledRecipe) => getEventsForRecipe(compiledRecipe)
      case ProcessDeleted(_) => throw new ProcessDeletedException(s"Process $processId is deleted")
      case ProcessUninitialized(_) => throw new NoSuchProcessException(s"No process found for $processId")
      case _ => throw new BakerException("Unknown response received")
    }
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
        case instanceState: InstanceState => Future.successful(instanceState.state.asInstanceOf[ProcessState])
        case Uninitialized(id) => Future.failed(new NoSuchProcessException(s"No such process with: $id"))
        case ProcessUninitialized(id) => Future.failed(new NoSuchProcessException(s"No such process with: $id"))
        case ProcessDeleted(id) => Future.failed(new ProcessDeletedException(s"Process $id is deleted"))
        case msg => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
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
          eventNames = this.events(processId).map(_.name).toSet,
          ingredientNames = this.getIngredients(processId).keySet)
      case ProcessDeleted(_) => throw new ProcessDeletedException(s"Process $processId is deleted")
      case Uninitialized(_) => throw new NoSuchProcessException(s"Process $processId is not found")
    }
  }

  private def doRegisterEventListener(listener: EventListener, fn: String => Boolean): Boolean = {
    val subscriber = actorSystem.actorOf(Props(new Actor() {
      override def receive: Receive = {
        case ProcessInstanceEvent(processType, processId, event: TransitionFiredEvent[_, _, _]) if fn(processType) =>
          toRuntimeEvent(event).foreach(e => listener.processEvent(processId, e))
        case ProcessInstanceEvent(processType, processId, event: TransitionFailedEvent[_, _, _]) if fn(processType) =>
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
  def registerEventListener(listener: EventListener): Boolean =
    doRegisterEventListener(listener, _ => true)


  def addInteractionImplementation(implementation: AnyRef) =
    MethodInteractionImplementation.anyRefToInteractionImplementations(implementation).foreach(interactionManager.add)

  def addInteractionImplementations(implementations: Seq[AnyRef]) =
    implementations.foreach(addInteractionImplementation)

  def addInteractionImplementation(interactionImplementation: InteractionImplementation) =
    interactionManager.add(interactionImplementation)

  if (!config.as[Option[Boolean]]("baker.config-file-included").getOrElse(false))
    throw new IllegalStateException("You must 'include baker.conf' in your application.conf")

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
