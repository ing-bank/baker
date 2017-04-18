package com.ing.baker.core

import java.util.UUID

import akka.NotUsed
import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.pattern.ask
import akka.persistence.query.PersistenceQuery
import akka.persistence.query.scaladsl._
import akka.stream.ActorMaterializer
import akka.stream.scaladsl.{Sink, Source}
import akka.util.Timeout
import com.ing.baker.RecipeVisualizer
import com.ing.baker.actor._
import com.ing.baker.compiler.{CompiledRecipe, RecipeCompiler, ValidationSettings, _}
import com.ing.baker.scala_api.BakerResponse
import fs2.Strategy
import io.kagera.akka.actor.PetriNetInstanceProtocol._
import io.kagera.akka.actor._
import io.kagera.akka.query.PetriNetQuery
import io.kagera.execution.EventSourcing.TransitionFiredEvent
import io.kagera.persistence.Encryption
import io.kagera.persistence.Encryption.NoEncryption
import net.ceedubs.ficus.Ficus._
import org.slf4j.LoggerFactory

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}
import scala.language.postfixOps
import scala.util.{Failure, Success, Try}

/**
  * The Baker knows:
  * - A recipe
  * - The ingredientImpls (what concrete implementation for what interface): Map[Interface, Implementation]
  * - A list of events
  * The Baker can bake a recipe, create a process and respond to events.
  */
class Baker(val recipe: Recipe,
            val implementations: Map[Class[_], () => AnyRef],
            val validationSettings: ValidationSettings = ValidationSettings.defaultValidationSettings,
            implicit val actorSystem: ActorSystem) {

  val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe, implementations, validationSettings,  new CompositeIngredientExtractor(actorSystem.settings.config))

  if (compiledRecipe.validationErrors.nonEmpty)
    throw new RecipeValidationException(compiledRecipe.validationErrors.mkString(", "))

  RecipeValidations.assertEventsAndIngredientsAreSerializable(compiledRecipe)

  import actorSystem.dispatcher

  implicit val materializer = ActorMaterializer()

  private val log = LoggerFactory.getLogger(classOf[Baker])

  private val config = actorSystem.settings.config
  private val bakeTimeout = config.as[FiniteDuration]("baker.bake-timeout")
  private val journalInitializeTimeout = config.as[FiniteDuration]("baker.journal-initialize-timeout")
  private val readJournalIdentifier = config.as[String]("baker.actor.read-journal-plugin")

  /**
    * We do this to force initialization of the journal (database) connection.
    */
  com.ing.baker.actor.Util.createPersistenceWarmupActor()(actorSystem, journalInitializeTimeout)

  private val bakerActorProvider =
    actorSystem.settings.config.as[Option[String]]("baker.actor.provider") match {
      case None | Some("local") => new LocalBakerActorProvider
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

  private val processIdManagerActor = bakerActorProvider.createActorIndex(
    compiledRecipe.name,
    PetriNetInstance.props[ProcessState](compiledRecipe.petriNet,
      PetriNetInstance.Settings(
        evaluationStrategy = Strategy.fromCachedDaemonPool("Baker.CachedThreadpool"),
        serializer = new AkkaObjectSerializer(actorSystem, configuredEncryption),
        idleTTL = actorIdleTimeout )))

  private val petriNetApi = new PetriNetInstanceApi[ProcessState](compiledRecipe.petriNet, processIdManagerActor)

  private val readJournal = PersistenceQuery(actorSystem)
    .readJournalFor[CurrentEventsByPersistenceIdQuery with AllPersistenceIdsQuery with CurrentPersistenceIdsQuery](readJournalIdentifier)

  private def createEventMsg(processId: java.util.UUID, event: AnyRef) = {
    require(event != null, "Event can not be null")

    val t = compiledRecipe.transitionForEventClass(event.getClass)
    BakerActorMessage(processId, FireTransition(t.id, event))
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
        implicit val akkaTimeout = Timeout(timeout);
        Util.handOverShardsAndLeaveCluster(Seq(recipe.name))
      case Success(cluster) =>
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

    val msg = Initialize(compiledRecipe.initialMarking, ProcessState(processId, Map.empty))
    val initializeFuture = (processIdManagerActor ? BakerActorMessage(processId, msg)).mapTo[Response]

    val eventualState = initializeFuture.map {
      case msg: Initialized   => msg.state.asInstanceOf[ProcessState]
      case AlreadyInitialized => throw new IllegalArgumentException(s"Processs with $processId already exists.")
      case msg @ _            => throw new BakerException(s"Unexpected message: $msg")
    }

    eventualState
  }

  /**
    * Synchronously returns all events that occurred for a process.
    */
  def events(processId: java.util.UUID)(implicit timeout: FiniteDuration): Seq[Any] = {

    val futureEventSeq = eventsAsync(processId).runWith(Sink.seq)

    Await.result(futureEventSeq, timeout)
  }

  /**
    * Returns a Source of baker events for a process.
    *
    * @param processId The process identifier.
    * @return The source of events.
    */
  def eventsAsync(processId: java.util.UUID): Source[Any, NotUsed] = {
    PetriNetQuery
      .eventsForInstance[ProcessState](processId.toString, compiledRecipe.petriNet, configuredEncryption, readJournal)
      .collect {
        case (_, TransitionFiredEvent(_, _, _, _, _, _, Some(output)))
          if compiledRecipe.allEvents.exists(_.isInstance(output)) => output
      }
  }

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * @param processId The process id
    * @param event     The event instance
    */
  def handleEvent(processId: java.util.UUID, event: AnyRef)(implicit timeout: FiniteDuration): Unit = {
    handleEventAsync(processId, event).confirmCompleted
  }

  /**
    * Fires an event to baker for a process. This is fire and forget in the sense that if nothing is done
    * with the response you have NO guarantee that the event is received by baker.
    */
  def handleEventAsync(processId: UUID, event: AnyRef): BakerResponse = {

    val msg = createEventMsg(processId, event)
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

  def getVisualState(processId: java.util.UUID)(implicit timeout: FiniteDuration): String = {
    val events: Seq[Any] = this.events(processId)
    val classes: Seq[String] = events.map(x => x.getClass.getSimpleName)
    RecipeVisualizer.generateDot(compiledRecipe.petriNet.innerGraph, x => true, classes)
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
    processIdManagerActor
      .ask(BakerActorMessage(processId, GetState))(Timeout.durationToTimeout(timeout))
      .map {
        case instanceState: InstanceState => instanceState.state.asInstanceOf[ProcessState]
        case Uninitialized(id) => throw new NoSuchProcessException(s"No such process with: $id")
        case msg => throw new BakerException(s"Unexpected actor response message: $msg")
      }
  }
}
