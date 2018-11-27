package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem, Address, AddressFromURIString, PoisonPill}
import akka.cluster.Cluster
import akka.cluster.sharding.ShardRegion._
import akka.cluster.sharding.{ClusterSharding, ClusterShardingSettings, ShardRegion}
import akka.cluster.singleton.{ClusterSingletonManager, ClusterSingletonManagerSettings, ClusterSingletonProxy, ClusterSingletonProxySettings}
import akka.stream.Materializer
import akka.util.Timeout
import com.ing.baker.il.sha256HashCode
import com.ing.baker.runtime.actor.ClusterBakerActorProvider._
import com.ing.baker.runtime.actor.process_index.ProcessIndex.{ActorMetadata, CheckForProcessesToBeDeleted}
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.actor.process_index._
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager
import com.ing.baker.runtime.actor.serialization.{BakerProtoMessage, Encryption}
import com.ing.baker.runtime.core.BakerException
import com.ing.baker.runtime.core.internal.InteractionManager
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._
import org.slf4j.LoggerFactory

import scala.concurrent.{Await, TimeoutException}
import scala.concurrent.duration._

object ClusterBakerActorProvider {

  case class GetShardIndex(entityId: String) extends BakerProtoMessage

  /**
    * This function calculates the names of the ActorIndex actors
    * gets the least significant bits of the UUID, and returns the MOD 10
    * So we have at most 10 manager actors created, all the petrinet actors will fall under these 10 actors
    * Note, the nrOfShards used here has to be aligned with the nrOfShards used in the shardIdExtractor
    */
  def entityId(processId: String, nrOfShards: Int): String =
    s"index-${Math.abs(sha256HashCode(processId) % nrOfShards)}"

  // extracts the actor id -> message from the incoming message
  // Entity id is the first character of the UUID
  def entityIdExtractor(nrOfShards: Int): ExtractEntityId = {
    case msg:ProcessIndexMessage => (entityId(msg.processId, nrOfShards), msg)
    case GetShardIndex(entityId) => (entityId, GetIndex)
    case msg => throw new IllegalArgumentException(s"Message of type ${msg.getClass} not recognized")
  }

  // extracts the shard id from the incoming message
  def shardIdExtractor(nrOfShards: Int): ExtractShardId = {
    case msg:ProcessIndexMessage => Math.abs(sha256HashCode(msg.processId) % nrOfShards).toString
    case GetShardIndex(entityId) => entityId.split(s"index-").last
    case ShardRegion.StartEntity(entityId) => entityId.split(s"index-").last
    case msg => throw new IllegalArgumentException(s"Message of type ${msg.getClass} not recognized")
  }

  val recipeManagerName = "RecipeManager"
}

class ClusterBakerActorProvider(config: Config, configuredEncryption: Encryption) extends BakerActorProvider {

  private val log = LoggerFactory.getLogger(classOf[ClusterBakerActorProvider])

  private val nrOfShards = config.as[Int]("baker.actor.cluster.nr-of-shards")
  private val retentionCheckInterval = config.as[FiniteDuration]("baker.actor.retention-check-interval")
  private val actorIdleTimeout: Option[FiniteDuration] = config.as[Option[FiniteDuration]]("baker.actor.idle-timeout")

  private val journalInitializeTimeout = config.as[FiniteDuration]("baker.journal-initialize-timeout")

  private def initializeCluster()(implicit actorSystem: ActorSystem) = {

    val seedNodes: List[Address] = config.as[Option[List[String]]]("baker.cluster.seed-nodes") match {
      case Some(_seedNodes) if _seedNodes.nonEmpty =>
        _seedNodes map AddressFromURIString.parse
      case None =>
        throw new BakerException("Baker cluster configuration without baker.cluster.seed-nodes")
    }

    /**
      * Join cluster after waiting for the persistenceInit actor, otherwise terminate here.
      */
    try {
      Await.result(Util.persistenceInit(journalInitializeTimeout), journalInitializeTimeout)
    } catch {
      case _: TimeoutException => throw new IllegalStateException(s"Timeout when trying to initialize the akka journal, waited $journalInitializeTimeout")
    }

    // join the cluster
    log.info("PersistenceInit actor started successfully, joining cluster seed nodes {}", seedNodes)
    Cluster.get(actorSystem).joinSeedNodes(seedNodes)
  }


  override def createProcessIndexActor(interactionManager: InteractionManager, recipeManager: ActorRef)(implicit actorSystem: ActorSystem, materializer: Materializer): ActorRef = {

    ClusterSharding(actorSystem).start(
      typeName = "ProcessIndexActor",
      entityProps = ProcessIndex.props(actorIdleTimeout, Some(retentionCheckInterval), configuredEncryption, interactionManager, recipeManager),
      settings = ClusterShardingSettings.create(actorSystem),
      extractEntityId = ClusterBakerActorProvider.entityIdExtractor(nrOfShards),
      extractShardId = ClusterBakerActorProvider.shardIdExtractor(nrOfShards)
    )
  }

  override def createRecipeManagerActor()(implicit actorSystem: ActorSystem, materializer: Materializer): ActorRef = {

    initializeCluster()

    val singletonManagerProps = ClusterSingletonManager.props(
      RecipeManager.props(),
      terminationMessage = PoisonPill,
      settings = ClusterSingletonManagerSettings(actorSystem))

    actorSystem.actorOf(props = singletonManagerProps, name = recipeManagerName)

    val singletonProxyProps = ClusterSingletonProxy.props(
      singletonManagerPath = s"/user/$recipeManagerName",
      settings = ClusterSingletonProxySettings(actorSystem))

    actorSystem.actorOf(props = singletonProxyProps, name = "RecipeManagerProxy")
  }

  def getIndex(actor: ActorRef)(implicit system: ActorSystem, timeout: FiniteDuration) = {

    import akka.pattern.ask
    import system.dispatcher
    implicit val akkaTimeout: Timeout = timeout

    val futures = (0 to nrOfShards).map { shard => actor.ask(GetShardIndex(s"index-$shard")).mapTo[Index].map(_.entries) }
    val collected: Seq[ActorMetadata] = Util.collectFuturesWithin(futures, timeout, system.scheduler).flatten

    collected
  }
}