package com.ing.baker.runtime.core

import java.util.concurrent.ConcurrentHashMap

import akka.actor.{ActorSystem, Address, AddressFromURIString}
import akka.cluster.Cluster
import akka.persistence.query.PersistenceQuery
import akka.persistence.query.scaladsl._
import akka.stream.ActorMaterializer
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

import scala.compat.java8.FunctionConverters._
import scala.collection.JavaConverters._
import scala.concurrent.Await
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

  import scala.compat.java8.FunctionConverters

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

  val recipeHandlers: ConcurrentHashMap[String, RecipeHandler] = new ConcurrentHashMap[String, RecipeHandler]()

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
  def addRecipe(compiledRecipe: CompiledRecipe): RecipeHandler = {

    val recipeHandlerProvider: String => RecipeHandler = _ => new RecipeHandler(
      compiledRecipe,
      interactionManager,
      configuredEncryption,
      actorIdleTimeout,
      bakeTimeout,
      readJournal,
      bakerActorProvider)

    val recipeHandler = recipeHandlers.computeIfAbsent(compiledRecipe.name, recipeHandlerProvider.asJava)

    if (recipeHandler.compiledRecipe != compiledRecipe)
      throw new BakerException(s"Recipe with name '${compiledRecipe.name}' already exists")

    recipeHandler
  }

  def getRecipeHandler(name: String): RecipeHandler = {

    recipeHandlers.get(name) match {
      case null          => throw new BakerException(s"No Recipe Handler available for recipe with name: $name")
      case recipeHandler => recipeHandler
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
        Util.handOverShardsAndLeaveCluster(recipeHandlers.values.asScala.toSeq.map(_.compiledRecipe.name))
      case Success(_) =>
        log.debug("ActorSystem not a member of cluster")
        actorSystem.terminate()
      case Failure(exception) =>
        log.debug("Cluster not available for actor system", exception)
        actorSystem.terminate()
    }
  }

  def allProcessMetadata: Set[ProcessMetadata] = recipeHandlers.values.asScala.flatMap(_.recipeMetadata.getAll).toSet
}
