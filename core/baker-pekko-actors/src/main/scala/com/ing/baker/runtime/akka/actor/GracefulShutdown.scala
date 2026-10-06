package com.ing.baker.runtime.akka.actor

import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.pattern.ask
import akka.util.Timeout
import com.ing.baker.runtime.akka.actor.GracefulShutdownShardRegions.InitiateGracefulShutdown
import com.ing.baker.runtime.akka.internal.TimeoutUtil._
import com.typesafe.scalalogging.Logger
import org.slf4j.LoggerFactory

import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{ExecutionContextExecutor, Future, Promise}
import scala.util.{Failure, Success, Try}

object GracefulShutdown {

  @transient
  lazy val logger: Logger = Logger(LoggerFactory.getLogger(getClass.getName))

  def gracefulShutdownActorSystem(actorSystem: ActorSystem, timeout: FiniteDuration, terminateActorSystem: Boolean): Future[Any] = {
    implicit val ec: ExecutionContextExecutor = actorSystem.dispatcher

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
          promise.success(true)
          if (terminateActorSystem) {
            actorSystem.terminate()
          }
        }

        cluster.leave(cluster.selfAddress)

        promise.future.withTimeout(timeout, "Graceful shutdown timed out")

      case Success(_) =>
        logger.warn("Not a member of a cluster, no need for cluster-level graceful shutdown")
        if (terminateActorSystem) {
          logger.info("terminating the actor system")
          actorSystem.terminate().withTimeout(timeout, "terminating actor system timed out")
        } else Future.successful(())

      case Failure(exception) =>
        logger.warn("Cluster not available for actor system", exception)
        if (terminateActorSystem)
          actorSystem.terminate().withTimeout(timeout, "terminating actor system timed out")
        else Future.successful(())
    }
  }

  def gracefulShutdownShards(typeNames: Seq[String])(implicit timeout: Timeout, actorSystem: ActorSystem): Future[Any] = {
    // first hand over the shards
    val actor = actorSystem.actorOf(GracefulShutdownShardRegions.props(timeout.duration, typeNames))
    actor.ask(InitiateGracefulShutdown).withTimeout(timeout.duration, s"Graceful shutdown of shards timed out after $timeout")(actorSystem.dispatcher)
  }
}
