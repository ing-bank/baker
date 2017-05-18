package com.ing.baker.runtime.actor

import java.util.UUID

import akka.actor.{ActorRef, ActorSystem, Props}
import akka.cluster.sharding.ShardRegion._
import akka.cluster.sharding.{ClusterSharding, ClusterShardingSettings}
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._

object ShardedActorProvider {

  /**
    * This function calculates the names of the ActorIndex actors
    * gets the least significant bits of the UUID, and returns the MOD 10
    * So we have at most 10 manager actors created, all the petrinet actors will fall under these 10 actors
    * Note, the nrOfShards used here has to be aligned with the nrOfShards used in the shardIdExtractor
    */
  def indexActorName(recipeName: String, processId: UUID, nrOfShards: Int): String =
    s"$recipeName-index-${Math.abs(processId.getLeastSignificantBits % nrOfShards)}"

  // extracts the actor id -> message from the incoming message
  // Entity id is the first character of the UUID
  def entityIdExtractor(recipeName: String, nrOfShards: Int): ExtractEntityId = {
    case msg@BakerActorMessage(processId, _) => (indexActorName(recipeName, processId, nrOfShards), msg)
  }

  // extracts the shard id from the incoming message
  def shardIdExtractor(nrOfShards: Int): ExtractShardId = {
    case BakerActorMessage(processId, _) => Math.abs(processId.getLeastSignificantBits % nrOfShards).toString
  }
}

class ShardedActorProvider(config: Config) extends BakerActorProvider {

  private val nrOfShards = config.as[Int]("baker.actor.cluster.nr-of-shards")

  override def createActorIndex(recipeName: String, petriNetActorProps: Props)(
    implicit actorSystem: ActorSystem): ActorRef = {
    ClusterSharding(actorSystem).start(
      typeName = recipeName,
      entityProps = ActorIndex.props(petriNetActorProps),
      settings = ClusterShardingSettings.create(actorSystem),
      extractEntityId = ShardedActorProvider.entityIdExtractor(recipeName, nrOfShards),
      extractShardId = ShardedActorProvider.shardIdExtractor(nrOfShards)
    )
  }
}