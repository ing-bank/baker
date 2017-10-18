package com.ing.baker.runtime.core

import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.actor.{Actor, ActorSystem, Props}
import akka.cluster.Cluster
import akka.pattern.ask
import akka.persistence.query.PersistenceQuery
import akka.persistence.query.scaladsl._
import akka.stream.ActorMaterializer
import akka.stream.scaladsl.Source
import akka.util.Timeout
import com.ing.baker.il._
import com.ing.baker.il.petrinet._
import com.ing.baker.petrinet.runtime.EventSourcing.TransitionFiredEvent
import com.ing.baker.runtime.actor._
import com.ing.baker.runtime.actor.serialization.Encryption
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import com.ing.baker.runtime.core.Baker._
import com.ing.baker.runtime.event_extractors.{CompositeEventExtractor, EventExtractor}
import com.ing.baker.runtime.petrinet.ReflectedInteractionTask
import net.ceedubs.ficus.Ficus._
import org.slf4j.LoggerFactory

import scala.concurrent.duration._
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
    if (t.isSensoryEvent || t.isInteraction)
      Some(event.output.asInstanceOf[RuntimeEvent])
    else
      None
  }
}

/**
  * The Baker knows:
  * - A recipe
  * - The interaction implementations for the interactions of the compiledRecipe (what concrete implementation for what interface): Map[Interface, Implementation]
  * - A list of events
  * The Baker can bake a recipe, create a process and respond to events.
  */
class Baker(val interactionFunctions: InteractionTransition[_] => (Seq[Any] => Any))
           (implicit val actorSystem: ActorSystem) {

  import actorSystem.dispatcher

  private val config = actorSystem.settings.config
  private val bakeTimeout = config.as[FiniteDuration]("baker.bake-timeout")
  private val journalInitializeTimeout = config.as[FiniteDuration]("baker.journal-initialize-timeout")
  private val readJournalIdentifier = config.as[String]("baker.actor.read-journal-plugin")
  private val actorIdleTimeout: Option[FiniteDuration] = config.as[Option[FiniteDuration]]("baker.actor.idle-timeout")
  implicit val materializer: ActorMaterializer = ActorMaterializer()
  private val log = LoggerFactory.getLogger(classOf[Baker])

  private val readJournal = PersistenceQuery(actorSystem)
    .readJournalFor[CurrentEventsByPersistenceIdQuery with PersistenceIdsQuery with CurrentPersistenceIdsQuery](readJournalIdentifier)

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

  var recipeHandlers: Seq[RecipeHandler] = Seq()

  def addRecipe(compiledRecipe: CompiledRecipe) = {
    recipeHandlers = recipeHandlers :+ new RecipeHandler(
      compiledRecipe,
      interactionFunctions,
      configuredEncryption,
      actorIdleTimeout,
      readJournal,
      bakerActorProvider)
  }

  def this(compiledRecipe: CompiledRecipe,
           implementations: Map[String, AnyRef])
          (implicit actorSystem: ActorSystem) = {
    this(ReflectedInteractionTask.createInteractionFunctions(compiledRecipe.interactionTransitions, implementations))(actorSystem)
    addRecipe(compiledRecipe)
  }

  def this(compiledRecipe: CompiledRecipe,
           implementations: Seq[(String, Seq[Any] => Any)])
          (implicit actorSystem: ActorSystem) = {
    this(Baker.toImplementations(implementations))
    addRecipe(compiledRecipe)
  }

  if (!config.as[Option[Boolean]]("baker.config-file-included").getOrElse(false))
    throw new IllegalStateException("You must 'include baker.conf' in your application.conf")


  /**
    * We do this to force initialization of the journal (database) connection.
    */
  Util.createPersistenceWarmupActor()(actorSystem, journalInitializeTimeout)


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
        Util.handOverShardsAndLeaveCluster(Seq(recipeHandlers(0).compiledRecipe.name))
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
  def bake(processId: String): ProcessState =
    Await.result(bakeAsync(processId), bakeTimeout)

  /**
    * Asynchronously creates an instance of the  process using the recipe.
    *
    * @param processId The process identifier
    * @return A future of the initial process state.
    */
  def bakeAsync(processId: String): Future[ProcessState] =
    recipeHandlers(0).bakeAsync(processId, bakeTimeout)


  /**
    * Registers a listener to all runtime events.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  def registerEventListener(listener: EventListener): Boolean = {

    val subscriber = actorSystem.actorOf(Props(new Actor() {
      override def receive: Receive = {
        case ProcessInstanceEvent(processType, id, event: TransitionFiredEvent[_, _, _])
          if processType == recipeHandlers(0).compiledRecipe.name =>
          toRuntimeEvent(event).foreach(e => listener.processEvent(id, e))
      }
    }))

    actorSystem.eventStream.subscribe(subscriber.actorRef, classOf[ProcessInstanceEvent])
  }

  /**
    * Synchronously returns all events that occurred for a process.
    */
  def events(processId: String)(implicit timeout: FiniteDuration): Seq[RuntimeEvent] = {
    recipeHandlers(0).events(processId)
  }

  /**
    * Returns a Source of baker events for a process.
    *
    * @param processId The process identifier.
    * @return The source of events.
    */
  def eventsAsync(processId: String): Source[RuntimeEvent, NotUsed] =
    recipeHandlers(0).eventsAsync(processId)


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
    recipeHandlers(0).handleEventAsync(processId, event)
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
  Await.result(recipeHandlers(0).getProcessStateAsync(processId), timeout)

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param processId The process identifier.
    * @param timeout   How long to wait to retreive the process state.
    * @return A visual (.dot) representation of the process state.
    */
  def getVisualState(processId: String)(implicit timeout: FiniteDuration): String = {
    recipeHandlers(0).getVisualState(processId)
  }

  /**
    * Returns a future of all the provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return A future of the provided ingredients.
    */
  def getIngredientsAsync(processId: String)(implicit timeout: FiniteDuration): Future[Map[String, Any]] = {
    recipeHandlers(0).getProcessStateAsync(processId).map(_.ingredients)
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

  def allProcessMetadata: Set[ProcessMetadata] = recipeHandlers.flatMap(_.recipeMetadata.getAll).toSet
}
