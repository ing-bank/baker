package com.ing.baker.runtime.akka.actor

import akka.actor._
import akka.cluster.sharding.{ClusterSharding, ShardRegion}
import com.ing.baker.runtime.akka.actor.GracefulShutdownShardRegions.{GracefulShutdownSuccessful, GracefulShutdownTimedOut, InitiateGracefulShutdown}

import scala.annotation.nowarn
import scala.collection._
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import scala.language.postfixOps

object GracefulShutdownShardRegions {

  case object InitiateGracefulShutdown

  case object GracefulShutdownTimedOut

  case object GracefulShutdownSuccessful

  def props(shardHandOverTimeout: FiniteDuration, typeNames: Seq[String]): Props =
    Props(new GracefulShutdownShardRegions(shardHandOverTimeout, typeNames))
}

class GracefulShutdownShardRegions(shardHandOverTimeout: FiniteDuration, typeNames: Seq[String]) extends Actor
  with ActorLogging {

  private val system = context.system

  // all the shard region actor refs
  private val shardRegionsRefs = typeNames.map(name => ClusterSharding(system).shardRegion(name)).toSet

  private implicit val ec: ExecutionContext = system.dispatcher

  override def receive: Receive = waitForLeaveCommand(shardRegionsRefs)

  def waitForLeaveCommand(regions: Set[ActorRef]): Receive = {
    case InitiateGracefulShutdown =>
      GracefulShutdown.logger.warn(s"Initiating graceful shut down of shard regions: ${typeNames.mkString(",")}")
      regions.foreach {region =>
        context watch region
        region ! ShardRegion.GracefulShutdown
      }
      context become waitingForTermination(regions, sender())
      context.system.scheduler.scheduleOnce(shardHandOverTimeout, context.self, GracefulShutdownTimedOut)
  }

  @nowarn
  def waitingForTermination(regions: Set[ActorRef], initiator: ActorRef): Receive = {
    case GracefulShutdownTimedOut =>
      GracefulShutdown.logger.warn(s"Graceful shutdown of shard regions timed out after $shardHandOverTimeout")
      context.stop(self)
    case Terminated(region) =>
      val newRegions = regions - region
      if (newRegions.isEmpty) {
        GracefulShutdown.logger.warn("Graceful shutdown of shard regions successful")
        initiator ! GracefulShutdownSuccessful
        context.stop(self)
      } else {
        context.become(waitingForTermination(newRegions, initiator))
      }
  }
}
