package com.ing.baker.runtime.actor

import akka.actor._
import akka.cluster.sharding.{ClusterSharding, ShardRegion}
import com.ing.baker.runtime.actor.GracefulShutdownShardRegions.{GracefulShutdownSuccessful, GracefulShutdownTimedOut, InitiateGracefulShutdown}
import com.typesafe.config.Config

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
  with ActorLogging  {

  val system = context.system

  // all the shard region actor refs
  val shardRegionsRefs = typeNames.map(name => ClusterSharding(system).shardRegion(name)).toSet

  implicit val ec: ExecutionContext = system.dispatcher

  val config: Config = system.settings.config

  override def receive = waitForLeaveCommand(shardRegionsRefs)

  def waitForLeaveCommand(regions: Set[ActorRef]): Receive = {
    case InitiateGracefulShutdown =>
      GracefulShutdown.log.warn(s"Initiating graceful shut down of shard regions: ${typeNames.mkString(",")}")
      regions.foreach { region =>
        context watch region
        region ! ShardRegion.GracefulShutdown
      }
      context become waitingForTermination(regions, sender())
      context.system.scheduler.scheduleOnce(shardHandOverTimeout, context.self, GracefulShutdownTimedOut)
  }

  def waitingForTermination(regions: Set[ActorRef], initiator: ActorRef): Receive = {
    case GracefulShutdownTimedOut      =>
      GracefulShutdown.log.warn(s"Graceful shutdown of shard regions timed out after $shardHandOverTimeout")
      context.stop(self)
    case Terminated(region) =>
      val newRegions = regions - region
      if (newRegions.isEmpty) {
        GracefulShutdown.log.warn("Graceful shutdown of shard regions successful")
        initiator ! GracefulShutdownSuccessful
        context.stop(self)
      } else
        context.become(waitingForTermination(newRegions, initiator))
  }
}
