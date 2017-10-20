package com.ing.baker.runtime.actor

import akka.actor.{ActorRef, ActorSystem}
import akka.cluster.Cluster
import akka.cluster.ddata.Replicator._
import akka.cluster.ddata._
import akka.pattern.ask
import akka.util.Timeout

import scala.concurrent.Await
import scala.concurrent.duration._

object ClusterRecipeMetadata {
  private val DataKey = ORSetKey.create[ProcessMetadata]("allProcessIds")
}

class ClusterRecipeMetadata(override val recipeName: String)(implicit actorSystem: ActorSystem) extends RecipeMetadata {

  import ClusterRecipeMetadata._

  implicit val timeout = Timeout(5 seconds)
  implicit val cluster = Cluster(actorSystem)

  private val replicator = DistributedData(actorSystem).replicator

  override def getAll: Set[ProcessMetadata] = {
    import actorSystem.dispatcher

    val resultFuture = replicator.ask(Get(DataKey, ReadMajority(timeout.duration))).mapTo[GetResponse[GSet[ProcessMetadata]]].map {
      case success: GetSuccess[_] => success.get(DataKey).elements
      case _: NotFound[_]         => Set.empty[ProcessMetadata]
      case msg                    => throw new IllegalStateException(s"Unexpected response: $msg")
    }

    Await.result(resultFuture, 5 seconds)
  }

  override def add(meta: ProcessMetadata): Unit = {
    replicator.tell(Update(DataKey, ORSet.empty[ProcessMetadata], WriteMajority(timeout.duration))(_ + meta), ActorRef.noSender)
  }

  override def remove(meta: ProcessMetadata): Unit = {
    replicator.tell(Update(DataKey, ORSet.empty[ProcessMetadata], WriteMajority(timeout.duration))(_ - meta), ActorRef.noSender)
  }
}
