package com.ing.baker.runtime.actor

import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.pattern.ask
import akka.util.Timeout
import com.ing.baker.runtime.actor.GracefulShutdownShardRegions.InitiateGracefulShutdown
import org.slf4j.LoggerFactory

import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{Await, Promise, TimeoutException}
import scala.util.{Failure, Success, Try}

object GracefulShutdown {

  val log = LoggerFactory.getLogger("com.ing.baker.runtime.actor.GracefulShutdown")

  def gracefulShutdownActorSystem(actorSystem: ActorSystem, timeout: FiniteDuration) = {

    Try {
      Cluster.get(actorSystem)
    } match {
      case Success(cluster) if cluster.state.members.exists(_.uniqueAddress == cluster.selfUniqueAddress) =>

        // gracefully shutdown (hand over) the shards
        gracefulShutdownShards(Seq("ProcessIndexActor"))(Timeout(timeout), actorSystem)

        // then leave the cluster
        log.warn("Leaving the akka cluster")

        val promise: Promise[Boolean] = Promise()

        cluster.registerOnMemberRemoved {
          log.warn("Successfully left the akka cluster, terminating the actor system")
          promise.success(true)
          actorSystem.terminate()
        }

        cluster.leave(cluster.selfAddress)

        Await.result(promise.future, timeout)

      case Success(_) =>
        log.warn("Not a member of a cluster, terminating the actor system")
        actorSystem.terminate()
      case Failure(exception) =>
        log.warn("Cluster not available for actor system", exception)
        actorSystem.terminate()
    }
  }

  def gracefulShutdownShards(typeNames: Seq[String])(implicit timeout: Timeout, actorSystem: ActorSystem): Unit = {
    // first hand over the shards
    val actor = actorSystem.actorOf(GracefulShutdownShardRegions.props(timeout.duration, typeNames))

    try {
      Await.result(actor.ask(InitiateGracefulShutdown), timeout.duration)
    } catch {
      case _: TimeoutException =>
        log.warn(s"Graceful shutdown of shards timed out after $timeout")
    }
  }
}
