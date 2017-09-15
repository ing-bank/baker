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
import com.ing.baker.runtime.actor.ProcessInstanceProtocol._
import com.ing.baker.petrinet.runtime.EventSourcing.TransitionFiredEvent
import com.ing.baker.petrinet.runtime.PetriNetRuntime
import com.ing.baker.runtime.actor._
import com.ing.baker.runtime.actor.serialization.{AkkaObjectSerializer, Encryption}
import com.ing.baker.runtime.core.Baker._
import com.ing.baker.runtime.event_extractors.{CompositeEventExtractor, EventExtractor}
import com.ing.baker.runtime.petrinet.{RecipeRuntime, ReflectedInteractionTask}
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
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

  val petriNetRuntime: PetriNetRuntime[Place, Transition, ProcessState, RuntimeEvent] = new RecipeRuntime(interactionFunctions)

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

  private def createEventMsg(processId: String, runtimeEvent: RuntimeEvent) = {
    require(runtimeEvent != null, "Event can not be null")
    val t: Transition[_, _] = transitionForRuntimeEvent(runtimeEvent, compiledRecipe)
    BakerActorMessage(processId, FireTransition(t.id, runtimeEvent))
  }

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
        case ProcessInstanceEvent(processType, id, event: TransitionFiredEvent[_,_,_]) if processType == compiledRecipe.name =>
            val t = event.transition.asInstanceOf[Transition[_,_]]
            if (t.isSensoryEvent || t.isInteraction)
              listener.processEvent(id, event.output.asInstanceOf[RuntimeEvent])
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
    * Fires an event to baker for a process. This call is fire and forget, meaning that if nothing is done
    * with the response object you haveSho NO guarantee that the event is received the process instance.
    */
  def handleEventAsync(processId: String, event: Any)(implicit timeout: FiniteDuration): BakerResponse = {

    val runtimeEvent = event match {
      case e: RuntimeEvent => e
      case e => Baker.eventExtractor.extractEvent(e)
    }

    if (!compiledRecipe.sensoryEvents.exists(runtimeEvent.isInstanceOfEventType(_)))
      throw new BakerException(s"Fired event ${runtimeEvent.name} is not recognised as any valid sensory event")

    val msg = createEventMsg(processId, runtimeEvent)
    val source = petriNetApi.askAndCollectAll(msg, waitForRetries = true)(timeout)
    new BakerResponse(processId, source)
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

  def getVisualState(processId: String)(implicit timeout: FiniteDuration): String = {
    RecipeVisualizer.visualiseCompiledRecipe(
      compiledRecipe,
      eventNames = this.events(processId).map(_.name).toSet,
      ingredientNames = this.getIngredients(processId).keySet)
  }


  /**
    * Get all state that is or was available in the Petri Net marking.
    *
    * @param processId The process id of the active process for which the accumulated state needs to be retrieved.
    * @return Accumulated state.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getIngredients(processId: String)(implicit timeout: FiniteDuration): Map[String, Any] =
    getProcessState(processId).ingredients

  /**
    * Get all state that is or was available in the Petri Net marking.
    *
    * @param processId The process id of the active process for which the accumulated state needs to be retrieved.
    * @return Accumulated state.
    */
  def getProcessStateAsync(processId: String)(implicit timeout: FiniteDuration): Future[ProcessState] = {
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
