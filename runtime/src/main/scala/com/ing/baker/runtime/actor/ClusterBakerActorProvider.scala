package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem, PoisonPill}
import akka.cluster.sharding.ShardRegion._
import akka.cluster.sharding.{ClusterSharding, ClusterShardingSettings, ShardRegion}
import akka.cluster.singleton.{ClusterSingletonManager, ClusterSingletonManagerSettings, ClusterSingletonProxy, ClusterSingletonProxySettings}
import com.ing.baker.il.sha256HashCode
import com.ing.baker.runtime.actor.processindex.ProcessIndex._
import com.ing.baker.runtime.actor.processindex._
import com.ing.baker.runtime.actor.recipemanager.RecipeManager
import com.ing.baker.runtime.actor.serialization.Encryption
import com.ing.baker.runtime.core.interations.InteractionManager
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._

import scala.concurrent.duration._
import ClusterBakerActorProvider._

object ClusterBakerActorProvider {

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
    case msg@CreateProcess(_, processId) => (entityId(processId, nrOfShards), msg)
    case msg@HandleEvent(processId, _) => (entityId(processId, nrOfShards), msg)
    case msg@GetProcessState(processId) => (entityId(processId, nrOfShards), msg)
    case msg@GetCompiledRecipe(processId) => (entityId(processId, nrOfShards), msg)
  }

  // extracts the shard id from the incoming message
  def shardIdExtractor(nrOfShards: Int): ExtractShardId = {
    case CreateProcess(_, processId) => Math.abs(sha256HashCode(processId) % nrOfShards).toString
    case HandleEvent(processId, _) => Math.abs(sha256HashCode(processId) % nrOfShards).toString
    case GetProcessState(processId) => Math.abs(sha256HashCode(processId) % nrOfShards).toString
    case GetCompiledRecipe(processId) => Math.abs(sha256HashCode(processId) % nrOfShards).toString
    case ShardRegion.StartEntity(entityId) => entityId.split(s"index-").last
  }

  val recipeManagerName = "RecipeManager"
}

class ClusterBakerActorProvider(config: Config, configuredEncryption: Encryption) extends BakerActorProvider {

  private val nrOfShards = config.as[Int]("baker.actor.cluster.nr-of-shards")
  private val retentionCheckInterval = config.as[Option[FiniteDuration]]("baker.actor.retention-check-interval").getOrElse(1 minute)
  private val distributedProcessMetadataEnabled = config.as[Boolean]("baker.distributed-process-metadata-enabled")
  private val actorIdleTimeout: Option[FiniteDuration] = config.as[Option[FiniteDuration]]("baker.actor.idle-timeout")

  override def createProcessIndexActor(interactionManager: InteractionManager, recipeManager: ActorRef)(implicit actorSystem: ActorSystem): (ActorRef, ProcessInstanceStore) = {
    val processInstanceStore = if (distributedProcessMetadataEnabled) new ClusterProcessInstanceStore()
    else new DisabledProcessInstanceStore
    val processIndexActor = ClusterSharding(actorSystem).start(
      typeName = "ProcessIndexActor",
      entityProps = ProcessIndex.props(processInstanceStore, retentionCheckInterval, actorIdleTimeout, configuredEncryption, interactionManager, recipeManager),
      settings = ClusterShardingSettings.create(actorSystem),
      extractEntityId = ClusterBakerActorProvider.entityIdExtractor(nrOfShards),
      extractShardId = ClusterBakerActorProvider.shardIdExtractor(nrOfShards)
    )
    (processIndexActor, processInstanceStore)
  }

  override def createRecipeManagerActor()(implicit actorSystem: ActorSystem): ActorRef = {

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
}