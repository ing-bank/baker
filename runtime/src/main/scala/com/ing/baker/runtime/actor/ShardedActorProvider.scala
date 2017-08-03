package com.ing.baker.runtime.actor

import akka.actor.{Actor, ActorLogging, ActorRef, ActorSystem, Props}
import akka.cluster.Cluster
import akka.cluster.ddata.Replicator._
import akka.cluster.ddata.{DistributedData, GSet, GSetKey}
import akka.cluster.sharding.ShardRegion._
import akka.cluster.sharding.{ClusterSharding, ClusterShardingSettings, ShardRegion}
import akka.pattern.ask
import akka.util.Timeout
import com.ing.baker.il.sha256HashCode
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._

import scala.concurrent.Await
import scala.concurrent.duration.{Duration, DurationDouble}

object ShardedActorProvider {

  /**
    * This function calculates the names of the ActorIndex actors
    * gets the least significant bits of the UUID, and returns the MOD 10
    * So we have at most 10 manager actors created, all the petrinet actors will fall under these 10 actors
    * Note, the nrOfShards used here has to be aligned with the nrOfShards used in the shardIdExtractor
    */
  def entityId(recipeName: String, processId: String, nrOfShards: Int): String =
    s"$recipeName-index-${Math.abs(sha256HashCode(processId) % nrOfShards)}"

  // extracts the actor id -> message from the incoming message
  // Entity id is the first character of the UUID
  def entityIdExtractor(recipeName: String, nrOfShards: Int): ExtractEntityId = {
    case msg@BakerActorMessage(processId, _) => (entityId(recipeName, processId, nrOfShards), msg)
  }

  // extracts the shard id from the incoming message
  def shardIdExtractor(recipeName: String, nrOfShards: Int): ExtractShardId = {
    case BakerActorMessage(processId, _)   => Math.abs(sha256HashCode(processId) % nrOfShards).toString
    case ShardRegion.StartEntity(entityId) => entityId.split(s"$recipeName-index-").last
  }
}

class ShardedActorProvider(config: Config) extends BakerActorProvider {

  private val nrOfShards = config.as[Int]("baker.actor.cluster.nr-of-shards")

  override def createRecipeActors(recipeName: String, receivePeriod: Duration, petriNetActorProps: Props)(
    implicit actorSystem: ActorSystem): (ActorRef, RecipeMetadata) = {
    val recipeMetadata = new ClusterRecipeMetadata(recipeName)
    val recipeManagerActor = ClusterSharding(actorSystem).start(
      typeName = recipeName,
      entityProps = ActorIndex.props(petriNetActorProps, recipeMetadata, recipeName, receivePeriod),
      settings = ClusterShardingSettings.create(actorSystem),
      extractEntityId = ShardedActorProvider.entityIdExtractor(recipeName, nrOfShards),
      extractShardId = ShardedActorProvider.shardIdExtractor(recipeName, nrOfShards)
    )
    (recipeManagerActor, recipeMetadata)
  }
}

object ClusterRecipeMetadata {
  private val DataKey = GSetKey.create[ProcessMetadata]("allProcessIds")
}

class ClusterRecipeMetadata(override val recipeName: String)(implicit actorSystem: ActorSystem) extends RecipeMetadata {

  import ClusterRecipeMetadata._

  implicit val timeout = Timeout(5 seconds)

  private val replicator = DistributedData(actorSystem).replicator
  implicit val node = Cluster(actorSystem)

  private val senderActor = actorSystem.actorOf(Props.apply(new Actor with ActorLogging {
    //noinspection TypeAnnotation
    override def receive = {
      case msg => log.debug("Ignoring message: {}", msg)
    }
  }))

  replicator ! Subscribe(DataKey, senderActor)

  override def getAllProcessMetadata: Set[ProcessMetadata] = {
    import actorSystem.dispatcher

    val resultFuture = replicator.ask(Get(DataKey, ReadMajority(timeout.duration))).mapTo[GetResponse[GSet[ProcessMetadata]]].map {
      case success: GetSuccess[_] => success.get(DataKey).elements
      case _: NotFound[_]         => Set.empty[ProcessMetadata]
      case msg                    => throw new IllegalStateException(s"Unexpected response: $msg")
    }

    Await.result(resultFuture, 5 seconds)
  }

  override def addNewProcessMetadata(name: String, created: Long): Unit = {
    replicator.tell(Update(DataKey, GSet.empty[ProcessMetadata], WriteMajority(timeout.duration))(_ + ProcessMetadata(name, created)), senderActor)
  }

}