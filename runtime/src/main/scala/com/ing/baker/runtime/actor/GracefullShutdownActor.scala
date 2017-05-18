package com.ing.baker.runtime.actor

import akka.actor._
import akka.cluster.sharding.{ClusterSharding, ShardRegion}
import com.ing.baker.runtime.actor.GracefulShutdownActor.{Done, Leave, ShardHandoverTimedOut}
import com.typesafe.config.Config

import scala.collection._
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import scala.language.postfixOps

object GracefulShutdownActor {

  case object Leave
  case object ShardHandoverTimedOut
  case object Done

  def props(shardHandOverTimeout: FiniteDuration, typeNames: Seq[String]): Props =
    Props(new GracefulShutdownActor(shardHandOverTimeout, typeNames))
}

class GracefulShutdownActor(shardHandOverTimeout: FiniteDuration, typeNames: Seq[String]) extends Actor
  with ActorLogging  {

  val system = context.system

  // all the shard region actor refs
  val shardRegionsRefs = typeNames.map(name => ClusterSharding(system).shardRegion(name)).toSet

  implicit val ec: ExecutionContext = system.dispatcher

  val config: Config = system.settings.config

  override def receive = waitForLeaveCommand(shardRegionsRefs)

  def waitForLeaveCommand(regions: Set[ActorRef]): Receive = {
    case Leave =>
      log.warning(s"Gracefully shutting down (handing over) regions: ${typeNames.mkString(",")}")
      regions.foreach { region =>
        context watch region
        region ! ShardRegion.GracefulShutdown
      }
      context become waitingForTermination(regions, sender())
      context.system.scheduler.scheduleOnce(shardHandOverTimeout, context.self, ShardHandoverTimedOut)
  }

  def waitingForTermination(regions: Set[ActorRef], initiator: ActorRef): Receive = {
    case ShardHandoverTimedOut      =>
      sendResponseAndStop(initiator)
    case Terminated(region) =>
      val newRegions = regions - region
      if (newRegions.isEmpty) {
        log.info("Shard regions handed over, leaving cluster and shutting down actor system")
        sendResponseAndStop(initiator)
      } else
        context.become(waitingForTermination(newRegions, initiator))
  }

  def sendResponseAndStop(leaveSender: ActorRef): Unit = {
    leaveSender ! Done
    context.stop(self)
  }
}
