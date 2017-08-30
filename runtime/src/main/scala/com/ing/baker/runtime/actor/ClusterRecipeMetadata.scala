package com.ing.baker.runtime.actor

import akka.actor.{Actor, ActorLogging, ActorSystem, Props}
import akka.util.Timeout
import akka.cluster.ddata._
import akka.cluster.ddata.Replicator._
import akka.cluster.Cluster
import scala.concurrent.duration._
import akka.pattern.ask

import scala.concurrent.Await

object ClusterRecipeMetadata {
  private val DataKey = ORSetKey.create[ProcessMetadata]("allProcessIds")
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
    replicator.tell(Update(DataKey, ORSet.empty[ProcessMetadata], WriteMajority(timeout.duration))(_ + meta), senderActor)
  }

  override def remove(meta: ProcessMetadata): Unit = {
    replicator.tell(Update(DataKey, ORSet.empty[ProcessMetadata], WriteMajority(timeout.duration))(_ - meta), senderActor)
  }
}
