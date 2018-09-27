package com.ing.baker.runtime.actor

import akka.actor.{Actor, ActorRef, ActorSystem, Address, AddressFromURIString, PoisonPill, Props}
import akka.cluster.Cluster
import akka.cluster.sharding.ShardRegion._
import akka.cluster.sharding.{ClusterSharding, ClusterShardingSettings, ShardRegion}
import akka.cluster.singleton.{ClusterSingletonManager, ClusterSingletonManagerSettings, ClusterSingletonProxy, ClusterSingletonProxySettings}
import akka.stream.Materializer
import com.ing.baker.il.sha256HashCode
import com.ing.baker.runtime.actor.ClusterBakerActorProvider._
import com.ing.baker.runtime.actor.process_index.ProcessIndex.ActorMetadata
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.actor.process_index._
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol.RecipeManagerMessage
import com.ing.baker.runtime.actor.serialization.Encryption
import com.ing.baker.runtime.core.BakerException
import com.ing.baker.runtime.core.interations.InteractionManager
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._
import org.slf4j.LoggerFactory

import scala.concurrent.duration._
import scala.concurrent.{Await, TimeoutException}

object ClusterBakerActorProvider {

  case class GetShardIndex(entityId: String) extends InternalBakerMessage
  case class GetShardActiveProcesses(entityId: String) extends InternalBakerMessage

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
    case msg:ProcessInstanceMessage        => (entityId(msg.processId, nrOfShards), msg)
    case GetShardIndex(entityId)           => (entityId, GetIndex)
    case GetShardActiveProcesses(entityId) => (entityId, GetActiveProcesses)
    case msg => throw new IllegalArgumentException(s"Message of type ${msg.getClass} not recognized")
  }

  // extracts the shard id from the incoming message
  def shardIdExtractor(nrOfShards: Int): ExtractShardId = {
    case msg:ProcessInstanceMessage        => Math.abs(sha256HashCode(msg.processId) % nrOfShards).toString
    case GetShardIndex(entityId)           => entityId.split(s"index-").last
    case GetShardActiveProcesses(entityId) => entityId.split(s"index-").last
    case ShardRegion.StartEntity(entityId) => entityId.split(s"index-").last
    case msg => throw new IllegalArgumentException(s"Message of type ${msg.getClass} not recognized")
  }

  val recipeManagerName = "RecipeManager"
}

class ClusterRouterActor(processIndex: ActorRef, nrOfShards: Int, recipeManager: ActorRef) extends Actor {

  val timeout = 2 seconds
  import akka.pattern.ask
  import context.dispatcher

  override def receive: Receive = {
    case ProcessIndexProtocol.GetIndex =>

      val futures = (0 to nrOfShards).map { shard => processIndex.ask(GetShardIndex(s"index-$shard"))(timeout).mapTo[Index].map(_.entries) }
      val collected: Seq[ActorMetadata] = Util.collectFuturesWithin(futures, timeout, context.system.scheduler).flatten

      sender() ! Index(collected)

    case ProcessIndexProtocol.GetActiveProcesses =>

      val futures = (0 to nrOfShards).map { shard => processIndex.ask(GetShardActiveProcesses(s"index-$shard"))(timeout).mapTo[Index].map(_.entries) }
      val collected: Seq[ActorMetadata] = Util.collectFuturesWithin(futures, timeout, context.system.scheduler).flatten

      sender() ! Index(collected)
    case msg: ProcessIndexMessage  => processIndex.forward(msg)
    case msg: RecipeManagerMessage => recipeManager.forward(msg)
  }
}

class ClusterBakerActorProvider(config: Config, configuredEncryption: Encryption) extends BakerActorProvider {

  private val log = LoggerFactory.getLogger(classOf[ClusterBakerActorProvider])

  private val nrOfShards = config.as[Int]("baker.actor.cluster.nr-of-shards")
  private val retentionCheckInterval = config.as[Option[FiniteDuration]]("baker.actor.retention-check-interval").getOrElse(1 minute)
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

  override def createBakerActor(interactionManager: InteractionManager)(implicit actorSystem: ActorSystem, materializer: Materializer): ActorRef = {

    initializeCluster()

    val singletonManagerProps = ClusterSingletonManager.props(
      RecipeManager.props(),
      terminationMessage = PoisonPill,
      settings = ClusterSingletonManagerSettings(actorSystem))

    actorSystem.actorOf(props = singletonManagerProps, name = recipeManagerName)

    val singletonProxyProps = ClusterSingletonProxy.props(
      singletonManagerPath = s"/user/$recipeManagerName",
      settings = ClusterSingletonProxySettings(actorSystem))

    val recipeManager = actorSystem.actorOf(props = singletonProxyProps, name = "RecipeManagerProxy")

    val processIndex = ClusterSharding(actorSystem).start(
      typeName = "ProcessIndexActor",
      entityProps = ProcessIndex.props(retentionCheckInterval, actorIdleTimeout, configuredEncryption, interactionManager, recipeManager),
      settings = ClusterShardingSettings.create(actorSystem),
      extractEntityId = ClusterBakerActorProvider.entityIdExtractor(nrOfShards),
      extractShardId = ClusterBakerActorProvider.shardIdExtractor(nrOfShards)
    )

    actorSystem.actorOf(Props(
      new ClusterRouterActor(processIndex, nrOfShards, recipeManager)
    ))
  }
}