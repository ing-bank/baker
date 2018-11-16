package com.ing.baker.runtime.actor.downing

import akka.actor.{Actor, Cancellable, Props}
import akka.cluster.ClusterEvent._
import akka.cluster._
import akka.event.{DiagnosticLoggingAdapter, Logging}
import com.ing.baker.runtime.actor.downing.SplitBrainResolverActor.ActOnSbrDecision

import scala.concurrent.duration._


private[downing] object SplitBrainResolverActor {
  def props(downRemovalMargin: FiniteDuration) = Props(classOf[SplitBrainResolverActor], downRemovalMargin, new MajorityStrategy())

  case object ActOnSbrDecision
}

private[downing] class SplitBrainResolverActor(downRemovalMargin: FiniteDuration, strategy: Strategy) extends Actor {

  val log: DiagnosticLoggingAdapter = Logging.getLogger(this)

  import context.dispatcher
  var memberStatusLastChanged: Map[UniqueAddress, Deadline] = Map()

  val cluster = Cluster(context.system)
  var actOnSbrDecisionTask: Cancellable = context.system.scheduler.schedule(0 seconds, downRemovalMargin / 2, self, ActOnSbrDecision)

  override def preStart(): Unit = {
    cluster.subscribe(self, ClusterEvent.InitialStateAsEvents, classOf[ClusterDomainEvent])
    super.preStart()
  }

  override def postStop(): Unit = {
    cluster.unsubscribe(self)
    actOnSbrDecisionTask.cancel()
    super.postStop()
  }

  override def receive: Receive = {

    // member events
    case MemberUp(member) =>
      log.info("Member up {}", member)
      memberStatusLastChanged -= member.uniqueAddress

    case MemberLeft(member) =>
      log.info("Member left {}", member)
      memberStatusLastChanged -= member.uniqueAddress

    case MemberExited(member) =>
      log.info("Member exited {}", member)
      memberStatusLastChanged -= member.uniqueAddress

    case MemberRemoved(member, previousStatus) =>
      log.info("Member removed {}, previous status {}", member, previousStatus)
      memberStatusLastChanged -= member.uniqueAddress

    // reachability events
    case UnreachableMember(member) =>
      log.info("Unreachable member {}", member)
      memberStatusLastChanged += (member.uniqueAddress -> Deadline.now.+(downRemovalMargin))

    case ReachableMember(member) =>
      log.info("Reachable member {}", member)
      memberStatusLastChanged -= member.uniqueAddress

    case ActOnSbrDecision =>
      log.info("act on sbr decision. self: {}", cluster.selfAddress)
      strategy.sbrDecision(ClusterHelper(cluster, memberStatusLastChanged))

    case _ => () // do nothing for other messages
  }
}
