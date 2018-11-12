package com.ing.baker.runtime.actor.downing

import akka.actor.{Actor, Cancellable, Props}
import akka.cluster.ClusterEvent._
import akka.cluster._
import akka.event.{DiagnosticLoggingAdapter, Logging}
import com.ing.baker.runtime.actor.downing.SplitBrainResolverActor.ActOnSbrDecision

import scala.collection.immutable.SortedSet
import scala.concurrent.duration.FiniteDuration

private[downing] object SplitBrainResolverActor {
  def props(downRemovalMargin: FiniteDuration) = Props(classOf[SplitBrainResolverActor], downRemovalMargin, new MajorityStrategy())

  case object ActOnSbrDecision
}

private[downing] class SplitBrainResolverActor(downRemovalMargin: FiniteDuration, strategy: Strategy) extends Actor {

  val log: DiagnosticLoggingAdapter = Logging.getLogger(this)

  import context.dispatcher
  var actOnSbrDecisionTask: Option[Cancellable] = Option(context.system.scheduler.scheduleOnce(downRemovalMargin, self, ActOnSbrDecision))

  val cluster = Cluster(context.system)
  val clusterHelper = ClusterHelper(cluster)

  override def preStart(): Unit = {
    cluster.subscribe(self, ClusterEvent.InitialStateAsEvents, classOf[ClusterDomainEvent])
    super.preStart()
  }

  override def postStop(): Unit = {
    cluster.unsubscribe(self)
    actOnSbrDecisionTask.foreach(_.cancel())
    super.postStop()
  }

  def scheduleSbrDecision(): Unit = {
    actOnSbrDecisionTask.foreach(_.cancel())
    actOnSbrDecisionTask = Option(cluster.system.scheduler.scheduleOnce(
      downRemovalMargin, self, ActOnSbrDecision
    ))
  }

  override def receive: Receive = {

    // member events
    case MemberUp(member) =>
      log.info("Member up {}", member)
      scheduleSbrDecision()

    case MemberLeft(member) =>
      log.info("Member left {}", member)
      scheduleSbrDecision()

    case MemberExited(member) =>
      log.info("Member exited {}", member)
      scheduleSbrDecision()

    case MemberRemoved(member, previousStatus) =>
      log.info("Member removed {}, previous status {}", member, previousStatus)
      scheduleSbrDecision()

    // cluster domain events
    case LeaderChanged(newLeader) =>
      log.info("Leader changed to {}", newLeader)
      scheduleSbrDecision()

    // reachability events
    case UnreachableMember(member) =>
      log.info("Unreachable member {}", member)
      scheduleSbrDecision()

    case ReachableMember(member) =>
      log.info("Reachable member {}", member)
      scheduleSbrDecision()

    case ActOnSbrDecision =>
      log.info("act on sbr decision. self: {}", cluster.selfAddress)
      strategy.sbrDecision(clusterHelper)

    case _ => () // do nothing for other messages

  }

}
