package com.ing.baker.runtime.core

import akka.actor.ActorSystem
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

import scala.concurrent.duration._
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
class Baker()(implicit val actorSystem: ActorSystem) {

  private val interactionManager: InteractionManager = new InteractionManager()
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

  def this(implementations: Seq[AnyRef])
          (implicit actorSystem: ActorSystem) = {
    this()(actorSystem)
    implementations.flatMap(MethodInteractionImplementation.anyRefToInteractionImplementations)
      .foreach(interactionManager.addInteractionImplementation)
  }

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
        Util.handOverShardsAndLeaveCluster(recipeHandlers.map(_.compiledRecipe.name))
      case Success(_) =>
        log.debug("ActorSystem not a member of cluster")
        actorSystem.terminate()
      case Failure(exception) =>
        log.debug("Cluster not available for actor system", exception)
        actorSystem.terminate()
    }
  }

  def allProcessMetadata: Set[ProcessMetadata] = recipeHandlers.flatMap(_.recipeMetadata.getAll).toSet
}
