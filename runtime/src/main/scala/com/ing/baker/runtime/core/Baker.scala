package com.ing.baker.runtime.core

import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.actor.{ActorSystem, Address, AddressFromURIString}
import akka.cluster.Cluster
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
import com.ing.baker.runtime.core.interations.{InteractionImplementation, InteractionManager, MethodInteractionImplementation}
import com.ing.baker.runtime.event_extractors.{CompositeEventExtractor, EventExtractor}
import net.ceedubs.ficus.Ficus._
import org.slf4j.LoggerFactory

import scala.concurrent.{Await, Future}
import scala.concurrent.duration.{FiniteDuration, _}
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
  private val actorIdleTimeout: Option[FiniteDuration] = config.as[Option[FiniteDuration]]("baker.actor.idle-timeout")
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

  private val bakerActorProvider =
    config.as[Option[String]]("baker.actor.provider") match {
      case None | Some("local")    =>
        new LocalBakerActorProvider(config)
      case Some("cluster-sharded") =>
        initializeCluster()
        new ClusterActorProvider(config)
      case Some(other)             =>
        throw new IllegalArgumentException(s"Unsupported actor provider: $other")
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

  def addRecipe(compiledRecipe: CompiledRecipe) : RecipeHandler = {
    if(recipeHandlers.exists(_.compiledRecipe.name == compiledRecipe.name))
      throw new BakerException("Recipe with this name already exists")

    val recipeHandler = new RecipeHandler(
      compiledRecipe,
      interactionManager,
      configuredEncryption,
      actorIdleTimeout,
      bakeTimeout,
      readJournal,
      bakerActorProvider)

    recipeHandlers = recipeHandlers :+ recipeHandler
    recipeHandler
  }

  def getRecipeHandler(name: String): RecipeHandler = {
    recipeHandlers.find(_.compiledRecipe.name == name) match {
      case Some(recipeHandler) => recipeHandler
      case None => throw new BakerException(s"No Recipe Handler available for recipe with name: $name")
    }
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
        Util.handOverShardsAndLeaveCluster(recipeHandlers.map(_.compiledRecipe.name))
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
  @deprecated("Use recipe handler instead" , "2.0.01")
  def bake(processId: String): ProcessState = recipeHandlers.head.bake(processId)

  /**
    * Asynchronously creates an instance of the  process using the recipe.
    *
    * @param processId The process identifier
    * @return A future of the initial process state.
    */
  @deprecated("Use recipe handler instead" , "2.0.01")
  def bakeAsync(processId: String): Future[ProcessState] =
    recipeHandlers.head.bakeAsync(processId)

  /**
    * Registers a listener to all runtime events.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  @deprecated("Use recipe handler instead" , "2.0.01")
  def registerEventListener(listener: EventListener): Boolean =
    recipeHandlers.head.registerEventListener(listener)

  /**
    * Synchronously returns all events that occurred for a process.
    */
  @deprecated("Use recipe handler instead" , "2.0.01")
  def events(processId: String)(implicit timeout: FiniteDuration): Seq[RuntimeEvent] =
    recipeHandlers.head.events(processId)(timeout)

  /**
    * Returns a Source of baker events for a process.
    *
    * @param processId The process identifier.
    * @return The source of events.
    */
  @deprecated("Use recipe handler instead" , "2.0.01")
  def eventsAsync(processId: String): Source[RuntimeEvent, NotUsed] =
    recipeHandlers.head.eventsAsync(processId)

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * @param processId The process identifier
    * @param event     The event object
    */
  @deprecated("Use recipe handler instead" , "2.0.01")
  def handleEvent(processId: String, event: Any)(implicit timeout: FiniteDuration): SensoryEventStatus =
    recipeHandlers.head.handleEvent(processId, event)

  /**
    * Fires an event to baker for a process.
    *
    * This call is fire and forget: If  nothing is done
    * with the response object you NO guarantee that the event is received the process instance.
    */
  @deprecated("Use recipe handler instead" , "2.0.01")
  def handleEventAsync(processId: String, event: Any)(implicit timeout: FiniteDuration): BakerResponse =
    recipeHandlers.head.handleEventAsync(processId, event)

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param processId The process identifier.
    * @param timeout How long to wait to retreive the process state.
    * @return A visual (.dot) representation of the process state.
    */
  @deprecated("Use recipe handler instead" , "2.0.01")
  def getVisualState(processId: String)(implicit timeout: FiniteDuration): String =
    recipeHandlers.head.getVisualState(processId)

  /**
    * Returns a future of all the provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return A future of the provided ingredients.
    */
  @deprecated("Use recipe handler instead" , "2.0.01")
  def getIngredientsAsync(processId: String)(implicit timeout: FiniteDuration): Future[Map[String, Any]] =
    recipeHandlers.head.getIngredientsAsync(processId)

  /**
    * Returns all provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return The provided ingredients.
    */
  @deprecated("Use recipe handler instead" , "2.0.01")
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getIngredients(processId: String)(implicit timeout: FiniteDuration): Map[String, Any] =
    recipeHandlers.head.getIngredients(processId)

  def allProcessMetadata: Set[ProcessMetadata] = recipeHandlers.flatMap(_.recipeMetadata.getAll).toSet
}
