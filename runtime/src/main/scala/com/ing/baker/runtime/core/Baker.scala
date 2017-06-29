package com.ing.baker.runtime.core

import java.util.UUID

import akka.NotUsed
import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.pattern.ask
import akka.persistence.query.PersistenceQuery
import akka.persistence.query.scaladsl._
import akka.serialization.SerializationExtension
import akka.stream.ActorMaterializer
import akka.stream.scaladsl.{Sink, Source}
import akka.util.Timeout
import com.ing.baker.il._
import com.ing.baker.il.petrinet._
import com.ing.baker.runtime.actor._
import com.ing.baker.runtime.core.Baker._
import com.ing.baker.runtime.event_extractors.{CompositeEventExtractor, EventExtractor}
import fs2.Strategy
import io.kagera.akka.actor.PetriNetInstanceProtocol._
import io.kagera.akka.actor._
import io.kagera.akka.query.PetriNetQuery
import io.kagera.api._
import io.kagera.runtime.EventSourcing.TransitionFiredEvent
import io.kagera.runtime.PetriNetRuntime
import io.kagera.runtime.persistence.Encryption
import io.kagera.runtime.persistence.Encryption.NoEncryption
import net.ceedubs.ficus.Ficus._
import org.slf4j.LoggerFactory

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}
import scala.language.postfixOps
import scala.util.{Failure, Success, Try}

object Baker {

  val eventExtractor: EventExtractor = new CompositeEventExtractor()

  def transitionForRuntimeEvent(runtimeEvent: RuntimeEvent, compiledRecipe: CompiledRecipe) =
    compiledRecipe.petriNet.transitions.findByLabel(runtimeEvent.name).getOrElse {
      throw new IllegalArgumentException(s"No such event known in recipe: $runtimeEvent")
    }

  @throws[NonSerializableException]
  def assertIngredientsAreSerializable(compiledRecipe: CompiledRecipe)(implicit actorSystem: ActorSystem): Unit = {
    val serialization = SerializationExtension(actorSystem)

    val hasAkkaSerializer = (clazz: Class[_]) => Try { serialization.serializerFor(clazz) }.isSuccess

    val ingredientSerializationErrors: Seq[String] =
      compiledRecipe.ingredients.mapValues(_.clazz)
        .filterNot{case (c, v) => hasAkkaSerializer(v) }
        .map{case (c, v) => s"Ingredient $c of $v is not serializable by akka"}.toSeq

    val allErrors: Seq[String] = ingredientSerializationErrors

    if (allErrors.nonEmpty) throw new NonSerializableException(allErrors.mkString(", "))
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
            val interactionFunctions: InteractionTransition[_] => (ProcessState => RuntimeEvent))
           (implicit val actorSystem: ActorSystem) {

  import actorSystem.dispatcher

  def this(compiledRecipe: CompiledRecipe,
           implementations: Map[String, AnyRef])
          (implicit actorSystem: ActorSystem) =
    this(compiledRecipe, ReflectedInteractionTask.createInteractionFunctions(compiledRecipe.interactionTransitions, implementations))(actorSystem)

  def this(compiledRecipe: CompiledRecipe,
           implementations: Seq[AnyRef])
          (implicit actorSystem: ActorSystem) =
    this(compiledRecipe, ReflectedInteractionTask.implementationsToProviderMap(implementations))(actorSystem)

  implicit val materializer = ActorMaterializer()
  private val log = LoggerFactory.getLogger(classOf[Baker])

  private val config = actorSystem.settings.config
  private val bakeTimeout = config.as[FiniteDuration]("baker.bake-timeout")
  private val journalInitializeTimeout = config.as[FiniteDuration]("baker.journal-initialize-timeout")
  private val readJournalIdentifier = config.as[String]("baker.actor.read-journal-plugin")

  if (compiledRecipe.validationErrors.nonEmpty)
    throw new RecipeValidationException(compiledRecipe.validationErrors.mkString(", "))

  //Validate if all events and ingredients are serializable
  assertIngredientsAreSerializable(compiledRecipe)

  /**
    * We do this to force initialization of the journal (database) connection.
    */
  Util.createPersistenceWarmupActor()(actorSystem, journalInitializeTimeout)

  private val bakerActorProvider =
    actorSystem.settings.config.as[Option[String]]("baker.actor.provider") match {
      case None | Some("local") => new LocalBakerActorProvider()
      case Some("cluster-sharded") => new ShardedActorProvider(config)
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
    Util.recipePetriNetProps(compiledRecipe.petriNet,petriNetRuntime,
      PetriNetInstance.Settings(
        evaluationStrategy = Strategy.fromCachedDaemonPool("Baker.CachedThreadPool"),
        serializer = new AkkaObjectSerializer(actorSystem, configuredEncryption),
        idleTTL = actorIdleTimeout))

  private val (recipeManagerActor, recipeMetadata) = bakerActorProvider.createRecipeActors(
    compiledRecipe.name, petriNetInstanceActorProps)

  private val petriNetApi = new PetriNetInstanceApi[Place, Transition, ProcessState](compiledRecipe.petriNet, recipeManagerActor)

  private val readJournal = PersistenceQuery(actorSystem)
    .readJournalFor[CurrentEventsByPersistenceIdQuery with AllPersistenceIdsQuery with CurrentPersistenceIdsQuery](readJournalIdentifier)

  private def createEventMsg(processId: java.util.UUID, runtimeEvent: RuntimeEvent) = {
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
    * Creates an instance of the  process using the recipe.
    *
    * @param processId A unique process id.
    */
  def bake(processId: java.util.UUID): ProcessState = Await.result(bakeAsync(processId), bakeTimeout)

  /**
    * Asynchronously creates an instance of the  process using the recipe.
    *
    * @param processId A unique process id.
    * @return A future of the initial process state.
    */
  def bakeAsync(processId: java.util.UUID): Future[ProcessState] = {
    implicit val askTimeout = Timeout(bakeTimeout)

    val msg = Initialize(marshal(compiledRecipe.initialMarking), ProcessState(processId, Map.empty))
    val initializeFuture = (recipeManagerActor ? BakerActorMessage(processId, msg)).mapTo[Response]

    val eventualState = initializeFuture.map {
      case msg: Initialized => msg.state.asInstanceOf[ProcessState]
      case AlreadyInitialized => throw new IllegalArgumentException(s"Processs with $processId already exists.")
      case msg@_ => throw new BakerException(s"Unexpected message: $msg")
    }

    eventualState
  }

  /**
    * Synchronously returns all events that occurred for a process.
    */
  def events(processId: java.util.UUID)(implicit timeout: FiniteDuration): Seq[RuntimeEvent] = {

    val futureEventSeq = eventsAsync(processId).runWith(Sink.seq)

    Await.result(futureEventSeq, timeout)
  }

  /**
    * Returns a Source of baker events for a process.
    *
    * @param processId The process identifier.
    * @return The source of events.
    */
  def eventsAsync(processId: java.util.UUID): Source[RuntimeEvent, NotUsed] = {
    PetriNetQuery
      .eventsForInstance[Place, Transition, ProcessState, RuntimeEvent](s"${compiledRecipe.name}-$processId", compiledRecipe.petriNet, configuredEncryption, readJournal, petriNetRuntime.eventSourceFn)
      .collect {
        case (_, TransitionFiredEvent(_, _, _, _, _, _, runtimeEvent: RuntimeEvent))
          if runtimeEvent != null && compiledRecipe.allEvents.exists(e => e.name equals runtimeEvent.name) => runtimeEvent
      }
  }

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * @param processId The process id
    * @param event     The event instance
    */
  def handleEvent(processId: java.util.UUID, event: Any)(implicit timeout: FiniteDuration): Unit = {
    handleEventAsync(processId, event).confirmCompleted
  }

  /**
    * Fires an event to baker for a process. This is fire and forget in the sense that if nothing is done
    * with the response you have NO guarantee that the event is received by baker.
    */
  def handleEventAsync(processId: UUID, event: Any): BakerResponse = {

    val runtimeEvent = Baker.eventExtractor.extractEvent(event)

    val eventType = compiledRecipe.sensoryEvents.find(se => se.name == runtimeEvent.name)
      .getOrElse(throw new BakerException(s"Fired event $event is not recognised as any valid sensory event"))

    val validatedEvent = runtimeEvent.validate(eventType)

    val msg = createEventMsg(processId, validatedEvent)
    val source = petriNetApi.askAndCollectAll(msg, waitForRetries = true)
    new BakerResponse(processId, source)
  }

  /**
    * Returns the process state.
    *
    * Throws a NoSuchProcessException when the process with the given identifier does not exist.
    *
    * @param processId The process identifier.
    * @return The process state.
    */
  def getProcessState(processId: java.util.UUID)(implicit timeout: FiniteDuration): ProcessState = {
    Await.result(getProcessStateAsync(processId), timeout)
  }

  //TODO, decide if Baker can visualise itself or is visualising part of the runtime that the compiler exposes also?
  def getVisualState(processId: java.util.UUID)(implicit timeout: FiniteDuration): String = {
    RecipeVisualizer.visualiseCompiledRecipe(compiledRecipe, events = this.events(processId).map(_.name))
  }


  /**
    * Get all state that is or was available in the Petri Net marking.
    *
    * @param processId The process id of the active process for which the accumulated state needs to be retrieved.
    * @return Accumulated state.
    */
  def getIngredients(processId: java.util.UUID)(implicit timeout: FiniteDuration): Map[String, Any] =
    getProcessState(processId).ingredients

  /**
    * Get all state that is or was available in the Petri Net marking.
    *
    * @param processId The process id of the active process for which the accumulated state needs to be retrieved.
    * @return Accumulated state.
    */
  def getProcessStateAsync(processId: java.util.UUID)(implicit timeout: FiniteDuration): Future[ProcessState] = {
    recipeManagerActor
      .ask(BakerActorMessage(processId, GetState))(Timeout.durationToTimeout(timeout))
      .map {
        case instanceState: InstanceState => instanceState.state.asInstanceOf[ProcessState]
        case Uninitialized(id) => throw new NoSuchProcessException(s"No such process with: $id")
        case msg => throw new BakerException(s"Unexpected actor response message: $msg")
      }
  }

  def allProcessMetadata: Set[ProcessMetadata] = recipeMetadata.getAllProcessMetadata
}
