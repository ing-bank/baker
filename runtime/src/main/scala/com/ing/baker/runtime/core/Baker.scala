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
import com.ing.baker.runtime.actor.processindex.ProcessIndex.{CreateProcess, GetCompiledRecipe, GetProcessState, HandleEvent}
import com.ing.baker.runtime.actor.processindex.{ProcessApi, ProcessInstanceStore, ProcessMetadata}
import com.ing.baker.runtime.actor.processinstance.ProcessInstanceEvent
import com.ing.baker.runtime.actor.processinstance.ProcessInstanceProtocol.{AlreadyInitialized, Initialized, InstanceState, RecipeNotAvailable, Response, Uninitialized}
import com.ing.baker.runtime.actor.recipemanager.RecipeManager._
import com.ing.baker.runtime.actor.serialization.Encryption
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import com.ing.baker.runtime.core.Baker._
import com.ing.baker.runtime.core.interations.{InteractionImplementation, InteractionManager, MethodInteractionImplementation}
import com.ing.baker.runtime.event_extractors.{CompositeEventExtractor, EventExtractor}
import com.ing.baker.runtime.petrinet.RecipeRuntime
import net.ceedubs.ficus.Ficus._
import org.slf4j.LoggerFactory

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.{FiniteDuration, _}
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
  * The Baker knows:
  * - A recipe
  * - The interaction implementations for the interactions of the compiledRecipe (what concrete implementation for what interface): Map[Interface, Implementation]
  * - A list of events
  * The Baker can bake a recipe, create a process and respond to events.
  */
class Baker()(implicit val actorSystem: ActorSystem) {

  private val interactionManager: InteractionManager = new InteractionManager()
  private val config = actorSystem.settings.config
  private val bakeTimeout = config.as[FiniteDuration]("baker.bake-timeout")
  private val journalInitializeTimeout = config.as[FiniteDuration]("baker.journal-initialize-timeout")
  private val readJournalIdentifier = config.as[String]("baker.actor.read-journal-plugin")
  private val log = LoggerFactory.getLogger(classOf[Baker])

  implicit val materializer: ActorMaterializer = ActorMaterializer()

  implicit val timeout: FiniteDuration = 5 seconds

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

  val (processIndexActor: ActorRef, processInstanceStore: ProcessInstanceStore) =
    bakerActorProvider.createProcessIndexActor(interactionManager, recipeManager)

  private val petriNetApi = new ProcessApi(processIndexActor)

  /**
    * Adds a recipe to baker and returns a handler for the recipe.
    *
    * This function is idempotent, if the same (equal) recipe was added earlier this will return the existing handler.
    *
    * If a different (not equal) recipe with the same name was added earlier this will throw an IllegalStateException.
    *
    * @param compiledRecipe The compiled recipe.
    * @return A handler for the recipe.
    */
  def addRecipe(compiledRecipe: CompiledRecipe): String = {

    val implementationErrors = checkIfValidImplementationsProvided(interactionManager, compiledRecipe.interactionTransitions)
    if (implementationErrors.nonEmpty)
      throw new BakerException(implementationErrors.mkString(", "))

    if (compiledRecipe.validationErrors.nonEmpty)
      throw new RecipeValidationException(compiledRecipe.validationErrors.mkString(", "))

    // TODO this is a synchronous ask on an actor which is considered bad practice, alternative?
    val futureResult = recipeManager.ask(AddRecipe(compiledRecipe))(timeout)
    Await.result(futureResult, timeout) match {
      case AddRecipeResponse(recipeId) => recipeId
      case _ => throw new BakerException(s"Unexpected error happened when adding recipe")
    }
  }

  def getRecipe(recipeId: String): CompiledRecipe = {
    // TODO this is a synchronous ask on an actor which is considered bad practice, alternative?
    val futureResult = recipeManager.ask(GetRecipe(recipeId))(timeout)
    Await.result(futureResult, timeout) match {
      case RecipeFound(compiledRecipe) => compiledRecipe
      case NoRecipeFound => throw new IllegalArgumentException(s"No recipe found for recipe with id: ${recipeId}")
    }
  }

  /**
    * Creates a process instance of this recipe.
    *
    * @param processId The process identifier
    */
  def bake(recipeId: String, processId: String): ProcessState =
    Await.result(bakeAsync(recipeId, processId), bakeTimeout)

  /**
    * Asynchronously creates an instance of the  process using the recipe.
    *
    * @param processId The process identifier
    * @return A future of the initial process state.
    */
  def bakeAsync(recipeId: String, processId: String): Future[ProcessState] = {
    implicit val askTimeout = Timeout(bakeTimeout)

    val msg = CreateProcess(recipeId, processId)
    val initializeFuture = (processIndexActor ? msg).mapTo[Response]

    val eventualState: Future[ProcessState] = initializeFuture.map {
      case msg: Initialized => msg.state.asInstanceOf[ProcessState]
      case AlreadyInitialized =>
        throw new IllegalArgumentException(s"Process with id '$processId' already exists.")
      case RecipeNotAvailable(_) => throw new IllegalArgumentException(s"Recipe with id '$recipeId' does ont exist.")
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
  def handleEvent(processId: String, event: Any)(implicit timeout: FiniteDuration): SensoryEventStatus = {
    handleEventAsync(processId, event).confirmCompleted()
  }

  /**
    * Fires an event to baker for a process.
    *
    * This call is fire and forget: If  nothing is done
    * with the response object you NO guarantee that the event is received the process instance.
    */
  def handleEventAsync(processId: String, event: Any)(implicit timeout: FiniteDuration): BakerResponse = {

    val runtimeEvent: RuntimeEvent = event match {
      case runtimeEvent: RuntimeEvent => runtimeEvent
      case _ => Baker.eventExtractor.extractEvent(event)
    }

    val source = petriNetApi.askAndCollectAll(HandleEvent(processId, runtimeEvent), waitForRetries = true)(timeout)
    new BakerResponse(processId, source)
  }

  /**
    * Synchronously returns all events that occurred for a process.
    */
  def events(processId: String)(implicit timeout: FiniteDuration): Seq[RuntimeEvent] = {
    val futureEventSeq = eventsAsync(processId).runWith(Sink.seq)
    Await.result(futureEventSeq, timeout)
  }

  /**
    * Returns a Source of baker events for a process.
    *
    * @param processId The process identifier.
    * @return The source of events.
    */
  def eventsAsync(processId: String): Source[RuntimeEvent, NotUsed] = {

    def getEventsForRecipe(compiledRecipe: CompiledRecipe) : Source[RuntimeEvent, NotUsed] = {
      ProcessQuery
        .eventsForInstance[Place, Transition, ProcessState, RuntimeEvent](compiledRecipe.name, processId.toString, compiledRecipe.petriNet, configuredEncryption, readJournal, RecipeRuntime.eventSourceFn)
        .collect {
          case (_, TransitionFiredEvent(_, _, _, _, _, _, runtimeEvent: RuntimeEvent))
            if runtimeEvent != null && compiledRecipe.allEvents.exists(e => e.name equals runtimeEvent.name) => runtimeEvent
        }
    }

    // TODO this is a synchronous ask on an actor which is considered bad practice, alternative?
    val futureResult = processIndexActor.ask(GetCompiledRecipe(processId))(timeout)
    Await.result(futureResult, timeout) match {
      case RecipeFound(compiledRecipe) => getEventsForRecipe(compiledRecipe)
      case Uninitialized(_) => throw new NoSuchProcessException(s"No process found for ${processId}")
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
  private def getProcessState(processId: String)(implicit timeout: FiniteDuration): ProcessState =
    Await.result(getProcessStateAsync(processId), timeout)

  def getProcessStateAsync(processId: String)(implicit timeout: FiniteDuration): Future[ProcessState] = {
    processIndexActor
      .ask(GetProcessState(processId))(Timeout.durationToTimeout(timeout))
      .flatMap {
        case instanceState: InstanceState => Future.successful(instanceState.state.asInstanceOf[ProcessState])
        case Uninitialized(id) => Future.failed(new NoSuchProcessException(s"No such process with: $id"))
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
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getIngredients(processId: String)(implicit timeout: FiniteDuration): Map[String, Any] =
    getProcessState(processId).ingredients

  /**
    * Returns a future of all the provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return A future of the provided ingredients.
    */
  def getIngredientsAsync(processId: String)(implicit timeout: FiniteDuration): Future[Map[String, Any]] = {
    getProcessStateAsync(processId).map(_.ingredients)
  }

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param processId The process identifier.
    * @param timeout   How long to wait to retreive the process state.
    * @return A visual (.dot) representation of the process state.
    */
  def getVisualState(processId: String)(implicit timeout: FiniteDuration): String = {
    // TODO this is a synchronous ask on an actor which is considered bad practice, alternative?
    val futureResult = processIndexActor.ask(GetCompiledRecipe(processId))(timeout)
    Await.result(futureResult, timeout) match {
      case RecipeFound(compiledRecipe) =>
        RecipeVisualizer.visualiseCompiledRecipe(
          compiledRecipe,
          eventNames = this.events(processId).map(_.name).toSet,
          ingredientNames = this.getIngredients(processId).keySet)
      case _ => throw new IllegalArgumentException(s"No process found for ${processId}")
    }
  }

  /**
    * Registers a listener to all runtime events.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  def registerEventListener(recipeName: String, listener: EventListener): Boolean = {
    val subscriber = actorSystem.actorOf(Props(new Actor() {
      override def receive: Receive = {
        case ProcessInstanceEvent(processType, processId, event: TransitionFiredEvent[_, _, _]) if processType == recipeName =>
          toRuntimeEvent(event).foreach(e => listener.handleEvent(processId, e))
        case ProcessInstanceEvent(processType, processId, event: TransitionFailedEvent[_, _, _]) if processType == recipeName =>
          event.exceptionStrategy match {
            case Continue(_, event: RuntimeEvent) =>
              listener.handleEvent(processId, event)
            case _ =>
          }
        case _: ProcessInstanceEvent => // purposely ignored in order to not have unnecessary unhandled messages logged
      }
    }))
    actorSystem.eventStream.subscribe(subscriber.actorRef, classOf[ProcessInstanceEvent])
  }

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
  def shutdown(timeout: FiniteDuration = 30 seconds): Unit = {
    Try {
      Cluster.get(actorSystem)
    } match {
      case Success(cluster) if cluster.state.members.exists(_.uniqueAddress == cluster.selfUniqueAddress) =>
        cluster.registerOnMemberRemoved {
          actorSystem.terminate()
        }
        implicit val akkaTimeout = Timeout(timeout)
        Util.handOverShardsAndLeaveCluster(Seq("ProcessIndexActor", "RecipeManager"))
      case Success(_) =>
        log.debug("ActorSystem not a member of cluster")
        actorSystem.terminate()
      case Failure(exception) =>
        log.debug("Cluster not available for actor system", exception)
        actorSystem.terminate()
    }
  }

  def allProcessMetadata: Set[ProcessMetadata] = processInstanceStore.getAll
}
