package com.ing.baker.runtime.core

import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.actor.{Actor, ActorSystem, Props}
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
import com.ing.baker.petrinet.runtime.PetriNetRuntime
import com.ing.baker.runtime.actor.ProcessIndex.ReceivePeriodExpired
import com.ing.baker.runtime.actor.ProcessInstanceProtocol._
import com.ing.baker.runtime.actor._
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import com.ing.baker.runtime.actor.serialization.{AkkaObjectSerializer, Encryption}
import com.ing.baker.runtime.core.Baker._
import com.ing.baker.runtime.event_extractors.{CompositeEventExtractor, EventExtractor}
import com.ing.baker.runtime.petrinet.{RecipeRuntime, ReflectedInteractionTask}
import fs2.Strategy
import net.ceedubs.ficus.Ficus._
import org.slf4j.LoggerFactory

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}
import scala.language.postfixOps
import scala.util.{Failure, Success, Try}

object Baker {

  val eventExtractor: EventExtractor = new CompositeEventExtractor()

  def transitionForRuntimeEvent(runtimeEvent: RuntimeEvent, compiledRecipe: CompiledRecipe): Transition[_, _] =
    compiledRecipe.petriNet.transitions.findByLabel(runtimeEvent.name).getOrElse {
      throw new IllegalArgumentException(s"No such event known in recipe: $runtimeEvent")
    }

  def toImplementations(seq: Seq[(String, Seq[Any] => Any)]): InteractionTransition[_] => (Seq[Any] => Any) = {
      val map = seq.toMap
      i => map(i.interactionName)
  }

  /**
    * Translates a petri net TransitionFiredEvent to an optional RuntimeEvent
    */
  def toRuntimeEvent[P[_], T[_,_], E](event: TransitionFiredEvent[P, T ,E]): Option[RuntimeEvent] = {
    val t = event.transition.asInstanceOf[Transition[_,_]]
    if ((t.isSensoryEvent || t.isInteraction) && event.output.isInstanceOf[RuntimeEvent])
      Some(event.output.asInstanceOf[RuntimeEvent])
    else
      None
  }

  private def createEventMsg(recipe: CompiledRecipe, processId: String, runtimeEvent: RuntimeEvent) = {
    require(runtimeEvent != null, "Event can not be null")
    val t: Transition[_, _] = transitionForRuntimeEvent(runtimeEvent, recipe)
    BakerActorMessage(processId, FireTransition(t.id, runtimeEvent))
  }
}

/**
  * The Baker knows:
  * - A recipe
  * - The interaction implementations for the interactions of the compiledRecipe (what concrete implementation for what interface): Map[Interface, Implementation]
  * - A list of events
  * The Baker can bake a recipe, create a process and respond to events.
  */
class Baker(val compiledRecipe: CompiledRecipe,
            val interactionFunctions: InteractionTransition[_] => (Seq[Any] => Any))
           (implicit val actorSystem: ActorSystem) {

  import actorSystem.dispatcher

  def this(compiledRecipe: CompiledRecipe,
           implementations: Map[String, AnyRef])
          (implicit actorSystem: ActorSystem) =
    this(compiledRecipe, ReflectedInteractionTask.createInteractionFunctions(compiledRecipe.interactionTransitions, implementations))(actorSystem)

  def this(compiledRecipe: CompiledRecipe,
           implementations: Seq[(String, Seq[Any] => Any)])
          (implicit actorSystem: ActorSystem) =
      this(compiledRecipe, Baker.toImplementations(implementations))

  private val config = actorSystem.settings.config

  if (!config.as[Option[Boolean]]("baker.config-file-included").getOrElse(false))
    throw new IllegalStateException("You must 'include baker.conf' in your application.conf")

  private val bakeTimeout = config.as[FiniteDuration]("baker.bake-timeout")
  private val journalInitializeTimeout = config.as[FiniteDuration]("baker.journal-initialize-timeout")
  private val readJournalIdentifier = config.as[String]("baker.actor.read-journal-plugin")

  implicit val materializer = ActorMaterializer()
  private val log = LoggerFactory.getLogger(classOf[Baker])

  if (compiledRecipe.validationErrors.nonEmpty)
    throw new RecipeValidationException(compiledRecipe.validationErrors.mkString(", "))

  /**
    * We do this to force initialization of the journal (database) connection.
    */
  Util.createPersistenceWarmupActor()(actorSystem, journalInitializeTimeout)

  private val bakerActorProvider =
    actorSystem.settings.config.as[Option[String]]("baker.actor.provider") match {
      case None | Some("local") => new LocalBakerActorProvider(config)
      case Some("cluster-sharded") => new ClusterActorProvider(config)
      case Some(other) => throw new IllegalArgumentException(s"Unsupported actor provider: $other")
    }

  private val configuredEncryption: Encryption = {
    val encryptionEnabled = config.getAs[Boolean]("baker.encryption.enabled").getOrElse(false)
    if (encryptionEnabled) {
      new Encryption.AESEncryption(config.getString("baker.encryption.secret"))
    } else {
      NoEncryption
    }
  }

  private val actorIdleTimeout = config.as[Option[FiniteDuration]]("baker.actor.idle-timeout")

  val petriNetRuntime: PetriNetRuntime[Place, Transition, ProcessState, RuntimeEvent] = new RecipeRuntime(compiledRecipe.name, interactionFunctions)

  private val petriNetInstanceActorProps =
    Util.recipePetriNetProps(compiledRecipe.name, compiledRecipe.petriNet, petriNetRuntime,
      ProcessInstance.Settings(
        evaluationStrategy = Strategy.fromCachedDaemonPool("Baker.CachedThreadPool"),
        serializer = new AkkaObjectSerializer(actorSystem, configuredEncryption),
        idleTTL = actorIdleTimeout))

  private val (recipeManagerActor, recipeMetadata) = bakerActorProvider.createRecipeActors(
    compiledRecipe, petriNetInstanceActorProps)

  private val petriNetApi = new ProcessApi(recipeManagerActor)

  private val readJournal = PersistenceQuery(actorSystem)
    .readJournalFor[CurrentEventsByPersistenceIdQuery with PersistenceIdsQuery with CurrentPersistenceIdsQuery](readJournalIdentifier)


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
        Util.handOverShardsAndLeaveCluster(Seq(compiledRecipe.name))
      case Success(_) =>
        log.debug("ActorSystem not a member of cluster")
        actorSystem.terminate()
      case Failure(exception) =>
        log.debug("Cluster not available for actor system", exception)
        actorSystem.terminate()
    }
  }

  /**
    * Creates a process instance of this recipe.
    *
    * @param processId The process identifier
    */
  def bake(processId: String): ProcessState = Await.result(bakeAsync(processId), bakeTimeout)

  /**
    * Asynchronously creates an instance of the  process using the recipe.
    *
    * @param processId The process identifier
    * @return A future of the initial process state.
    */
  def bakeAsync(processId: String): Future[ProcessState] = {
    implicit val askTimeout = Timeout(bakeTimeout)

    val msg = Initialize(marshal(compiledRecipe.initialMarking), ProcessState(processId, Map.empty))
    val initializeFuture = (recipeManagerActor ? BakerActorMessage(processId, msg)).mapTo[Response]

    val eventualState = initializeFuture.map {
      case msg: Initialized => msg.state.asInstanceOf[ProcessState]
      case AlreadyInitialized => throw new IllegalArgumentException(s"Process with id '$processId' for recipe '${compiledRecipe.name}' already exists.")
      case msg@_ => throw new BakerException(s"Unexpected message: $msg")
    }

    eventualState
  }

  /**
    * Registers a listener to all runtime events.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  def registerEventListener(listener: EventListener): Boolean = {

    val subscriber = actorSystem.actorOf(Props(new Actor() {
      override def receive: Receive = {
        case ProcessInstanceEvent(processType, processId, event: TransitionFiredEvent[_,_,_]) if processType == compiledRecipe.name =>
          toRuntimeEvent(event).foreach(e => listener.processEvent(processId, e))
        case ProcessInstanceEvent(processType, processId, event: TransitionFailedEvent[_,_,_]) if processType == compiledRecipe.name =>
          event.exceptionStrategy match {
            case Continue(_, event: RuntimeEvent) =>
              listener.processEvent(processId, event)
            case _ =>
          }
      }
    }))

    actorSystem.eventStream.subscribe(subscriber.actorRef, classOf[ProcessInstanceEvent])
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
    ProcessQuery
      .eventsForInstance[Place, Transition, ProcessState, RuntimeEvent](compiledRecipe.name, processId.toString, compiledRecipe.petriNet, configuredEncryption, readJournal, petriNetRuntime.eventSourceFn)
      .collect {
        case (_, TransitionFiredEvent(_, _, _, _, _, _, runtimeEvent: RuntimeEvent))
          if runtimeEvent != null && compiledRecipe.allEvents.exists(e => e.name equals runtimeEvent.name) => runtimeEvent
      }
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
    * Handles an event and awaits confirms the firing of a specific event.
    *
    * @param processId
    * @param event
    * @return
    */
  def handleEventAndWaitForEvent(processId: String, event: Any, eventName: String)(implicit timeout: FiniteDuration): SensoryEventStatus = {
    val stream = handleEventStream(processId, event)

    // TODO check in advance if the event can fire (using petri net coverability algorithm)

    val eventStatusFuture: Future[SensoryEventStatus] = stream.collect {
      case TransitionNotEnabled(_,_)                                       => SensoryEventStatus.FiringLimitMet
      case ReceivePeriodExpired                                            => SensoryEventStatus.ReceivePeriodExpired
      case TransitionFired(_, _, _, _, _, _, RuntimeEvent(`eventName`, _)) => SensoryEventStatus.EventFired
      case Uninitialized(processId)                                        => throw new NoSuchProcessException(processId)
    }.runWith(Sink.headOption)
      .map {
        case Some(status) => status
        case None         => SensoryEventStatus.EventNotFired
      }

    Await.result(eventStatusFuture, timeout)
  }


  private def handleEventStream(processId: String, event: Any)(implicit timeout: FiniteDuration): Source[Any, NotUsed] = {
    val runtimeEvent = Baker.eventExtractor.extractEvent(event)

    val sensoryEvent: EventType = compiledRecipe.sensoryEvents
      .find(_.name.equals(runtimeEvent.name))
      .getOrElse(throw new IllegalArgumentException(s"No event with name '${runtimeEvent.name}' found in the recipe"))

    val eventValidationErrors = runtimeEvent.validateEvent(sensoryEvent)

    if (eventValidationErrors.nonEmpty)
      throw new IllegalArgumentException("Invalid event: " + eventValidationErrors.mkString(","))

    val msg = createEventMsg(compiledRecipe, processId, runtimeEvent)
    petriNetApi.askAndCollectAll(msg, waitForRetries = true)(timeout)
  }

  /**
    * Fires an event to baker for a process.
    *
    * This call is fire and forget: If  nothing is done
    * with the response object you NO guarantee that the event is received the process instance.
    */
  def handleEventAsync(processId: String, event: Any)(implicit timeout: FiniteDuration): BakerResponse = {
    val stream = handleEventStream(processId, event)
    new BakerResponse(processId, stream)
  }

  /**
    * Returns the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getProcessState(processId: String)(implicit timeout: FiniteDuration): ProcessState =
    Await.result(getProcessStateAsync(processId), timeout)

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param processId The process identifier.
    * @param timeout How long to wait to retreive the process state.
    * @return A visual (.dot) representation of the process state.
    */
  def getVisualState(processId: String)(implicit timeout: FiniteDuration): String = {
    RecipeVisualizer.visualiseCompiledRecipe(
      compiledRecipe,
      eventNames = this.events(processId).map(_.name).toSet,
      ingredientNames = this.getIngredients(processId).keySet)
  }

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
    * Returns all provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return The provided ingredients.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getIngredients(processId: String)(implicit timeout: FiniteDuration): Map[String, Any] =
    getProcessState(processId).ingredients


  private def getProcessStateAsync(processId: String)(implicit timeout: FiniteDuration): Future[ProcessState] = {
    recipeManagerActor
      .ask(BakerActorMessage(processId, GetState))(Timeout.durationToTimeout(timeout))
      .flatMap {
        case instanceState: InstanceState => Future.successful(instanceState.state.asInstanceOf[ProcessState])
        case Uninitialized(id) => Future.failed(new NoSuchProcessException(s"No such process with: $id"))
        case msg => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
      }
  }

  def allProcessMetadata: Set[ProcessMetadata] = recipeMetadata.getAll
}
