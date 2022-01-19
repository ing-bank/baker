package com.ing.baker.runtime.akka.actor

import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.pattern.ask
import akka.util.Timeout
import com.ing.baker.runtime.akka.actor.GracefulShutdownShardRegions.InitiateGracefulShutdown
import com.typesafe.scalalogging.Logger
import org.slf4j.LoggerFactory
import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{ Await, Promise, TimeoutException }
import scala.util.{ Failure, Success, Try }

object GracefulShutdown {

  @transient
  lazy val logger: Logger = Logger(LoggerFactory.getLogger(getClass.getName))

  def gracefulShutdownActorSystem(actorSystem: ActorSystem, timeout: FiniteDuration): Any = {

    Try {
      Cluster.get(actorSystem)
    } match {
      case Success(cluster) if cluster.state.members.exists(_.uniqueAddress == cluster.selfUniqueAddress) =>

        // gracefully shutdown (hand over) the shards
        gracefulShutdownShards(Seq("ProcessIndexActor"))(Timeout(timeout), actorSystem)

        // then leave the cluster
        logger.warn("Leaving the akka cluster")

        val promise: Promise[Boolean] = Promise()

        cluster.registerOnMemberRemoved {
          logger.warn("Successfully left the akka cluster, terminating the actor system")
          Await.result(actorSystem.terminate(), timeout)
          promise.success(true)
        }

        cluster.leave(cluster.selfAddress)

        Await.result(promise.future, timeout)

      case Success(_) =>
        logger.warn("Not a member of a cluster, terminating the actor system")
        Await.result(actorSystem.terminate(), timeout)
      case Failure(exception) =>
        logger.warn("Cluster not available for actor system", exception)
        Await.result(actorSystem.terminate(), timeout)
    }
  }

  def gracefulShutdownShards(typeNames: Seq[String])(implicit timeout: Timeout, actorSystem: ActorSystem): Unit = {
    // first hand over the shards
    val actor = actorSystem.actorOf(GracefulShutdownShardRegions.props(timeout.duration, typeNames))

    try {
      Await.result(actor.ask(InitiateGracefulShutdown), timeout.duration)
    } catch {
      case _: TimeoutException =>
        logger.warn(s"Graceful shutdown of shards timed out after $timeout")
    }
  }
}
