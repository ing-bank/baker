package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem, Props}
import akka.cluster.sharding.ShardRegion._
import akka.cluster.sharding.{ClusterSharding, ClusterShardingSettings, ShardRegion}
import com.ing.baker.il.{CompiledRecipe, sha256HashCode}
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._

import scala.concurrent.duration.Duration

object ClusterActorProvider {

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

class ClusterActorProvider(config: Config) extends BakerActorProvider {

  private val nrOfShards = config.as[Int]("baker.actor.cluster.nr-of-shards")

  override def createRecipeActors(recipe: CompiledRecipe, petriNetActorProps: Props)(
    implicit actorSystem: ActorSystem): (ActorRef, RecipeMetadata) = {
    val recipeMetadata = new ClusterRecipeMetadata(recipe.name)
    val recipeManagerActor = ClusterSharding(actorSystem).start(
      typeName = recipe.name,
      entityProps = ProcessIndex.props(petriNetActorProps, recipeMetadata, recipe.name, recipe.eventReceivePeriod, recipe.retentionPeriod),
      settings = ClusterShardingSettings.create(actorSystem),
      extractEntityId = ClusterActorProvider.entityIdExtractor(recipe.name, nrOfShards),
      extractShardId = ClusterActorProvider.shardIdExtractor(recipe.name, nrOfShards)
    )
    (recipeManagerActor, recipeMetadata)
  }
}