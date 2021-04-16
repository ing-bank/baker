package com.ing.baker.runtime.akka.actor

import akka.actor.{ActorRef, ActorSystem, Address, PoisonPill}
import akka.cluster.Cluster
import akka.cluster.sharding.ShardRegion._
import akka.cluster.sharding.{ClusterSharding, ClusterShardingSettings, ShardRegion}
import akka.cluster.singleton.{ClusterSingletonManager, ClusterSingletonManagerSettings, ClusterSingletonProxy, ClusterSingletonProxySettings}
import akka.management.cluster.bootstrap.ClusterBootstrap
import akka.management.scaladsl.AkkaManagement
import akka.util.Timeout
import cats.data.NonEmptyList
import cats.effect.IO
import com.ing.baker.il.sha256HashCode
import com.ing.baker.runtime.akka.actor.ClusterBakerActorProvider._
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex.ActorMetadata
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.akka.actor.process_index._
import com.ing.baker.runtime.akka.actor.serialization.BakerSerializable
import com.ing.baker.runtime.model.InteractionsF
import com.ing.baker.runtime.serialization.Encryption
import com.ing.baker.runtime.{RecipeManager, RecipeManagerImpl}
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.duration._
import scala.concurrent.{Await, TimeoutException}

object ClusterBakerActorProvider {

  case class GetShardIndex(entityId: String) extends BakerSerializable

  sealed trait ClusterBootstrapMode

  case class SeedNodesList(nel: NonEmptyList[Address]) extends ClusterBootstrapMode

  case object ServiceDiscovery extends ClusterBootstrapMode

  /**
    * This function calculates the names of the ActorIndex actors
    * gets the least significant bits of the UUID, and returns the MOD 10
    * So we have at most 10 manager actors created, all the petrinet actors will fall under these 10 actors
    * Note, the nrOfShards used here has to be aligned with the nrOfShards used in the shardIdExtractor
    */
  def entityId(recipeInstanceId: String, nrOfShards: Int): String =
    s"index-${Math.abs(sha256HashCode(recipeInstanceId) % nrOfShards)}"

  // extracts the actor id -> message from the incoming message
  // Entity id is the first character of the UUID
  def entityIdExtractor(nrOfShards: Int): ExtractEntityId = {
    case msg: ProcessIndexMessage => (entityId(msg.recipeInstanceId, nrOfShards), msg)
    case GetShardIndex(entityId) => (entityId, GetIndex)
    case msg => throw new IllegalArgumentException(s"Message of type ${msg.getClass} not recognized")
  }

  // extracts the shard id from the incoming message
  def shardIdExtractor(nrOfShards: Int): ExtractShardId = {
    case msg: ProcessIndexMessage => Math.abs(sha256HashCode(msg.recipeInstanceId) % nrOfShards).toString
    case GetShardIndex(entityId) => entityId.split(s"index-").last
    case ShardRegion.StartEntity(entityId) => entityId.split(s"index-").last
    case msg => throw new IllegalArgumentException(s"Message of type ${msg.getClass} not recognized")
  }

  val recipeManagerName = "RecipeManager"
}

class ClusterBakerActorProvider(
                                 nrOfShards: Int,
                                 retentionCheckInterval: FiniteDuration,
                                 actorIdleTimeout: Option[FiniteDuration],
                                 journalInitializeTimeout: FiniteDuration,
                                 seedNodes: ClusterBootstrapMode,
                                 ingredientsFilter: List[String],
                                 configuredEncryption: Encryption
                               ) extends BakerActorProvider with LazyLogging {

  private def initializeCluster()(implicit actorSystem: ActorSystem): Unit = {
    /**
      * Join cluster after waiting for the persistenceInit actor, otherwise terminate here.
      */
    try {
      Await.result(Util.persistenceInit(journalInitializeTimeout), journalInitializeTimeout)
    } catch {
      case _: TimeoutException => throw new IllegalStateException(s"Timeout when trying to initialize the akka journal, waited $journalInitializeTimeout")
    }
    // join the cluster
    logger.info("PersistenceInit actor started successfully, joining cluster seed nodes {}", seedNodes)
    seedNodes match {
      case SeedNodesList(nel) =>
        Cluster.get(actorSystem).joinSeedNodes(nel.toList)
      case ServiceDiscovery =>
        AkkaManagement(actorSystem).start()
        ClusterBootstrap(actorSystem).start()
    }
  }


  override def createProcessIndexActor(interactionManager: InteractionsF[IO],
                                       recipeManager: RecipeManager)(implicit actorSystem: ActorSystem): ActorRef = {
    val roles = Cluster(actorSystem).selfRoles
    ClusterSharding(actorSystem).start(
      typeName = "ProcessIndexActor",
      entityProps = ProcessIndex.props(actorIdleTimeout, Some(retentionCheckInterval), configuredEncryption, interactionManager, recipeManager, ingredientsFilter),
      settings = {
        if (roles.contains("state-node"))
          ClusterShardingSettings(actorSystem).withRole("state-node")
        else
          ClusterShardingSettings(actorSystem)
      },
      extractEntityId = ClusterBakerActorProvider.entityIdExtractor(nrOfShards),
      extractShardId = ClusterBakerActorProvider.shardIdExtractor(nrOfShards)
    )
  }

  override def createRecipeManager()(implicit actorSystem: ActorSystem): RecipeManager = {
    // todo move to a more proper location
    initializeCluster()
    RecipeManagerImpl.pollingAware(actorSystem.dispatcher)
  }

  def getAllProcessesMetadata(actor: ActorRef)(implicit system: ActorSystem, timeout: FiniteDuration): Seq[ActorMetadata] = {

    import akka.pattern.ask
    import system.dispatcher
    implicit val akkaTimeout: Timeout = timeout

    val futures = (0 to nrOfShards).map { shard => actor.ask(GetShardIndex(s"index-$shard")).mapTo[Index].map(_.entries) }
    val collected: Seq[ActorMetadata] = Util.collectFuturesWithin(futures, timeout, system.scheduler).flatten

    collected
  }
}