package com.ing.baker.runtime.actor.downing

import akka.actor.{Actor, Cancellable, Props}
import akka.cluster.ClusterEvent._
import akka.cluster._
import akka.event.{DiagnosticLoggingAdapter, Logging}
import com.ing.baker.runtime.actor.downing.SplitBrainResolverActor.ActOnSbrDecision

import scala.concurrent.duration._


private[downing] object SplitBrainResolverActor {
  def props(stableAfterPeriod: FiniteDuration) = Props(classOf[SplitBrainResolverActor], stableAfterPeriod, new MajorityStrategy())

  case object ActOnSbrDecision
}

private[downing] class SplitBrainResolverActor(stableAfterPeriod: FiniteDuration, strategy: Strategy) extends Actor {

  val log: DiagnosticLoggingAdapter = Logging.getLogger(this)

  var memberStatusLastChanged: Map[UniqueAddress, Deadline] = Map()

  val cluster = Cluster(context.system)

  // Send the SBR triggers more often than the defined stable-after period to be quicker to catch all unreachable nodes within one time slot
  private val schedulerTickFrequency: FiniteDuration = stableAfterPeriod / 2

  import context.dispatcher
  val actOnSbrDecisionTask: Cancellable = context.system.scheduler.schedule(0 seconds, schedulerTickFrequency, self, ActOnSbrDecision)

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
      memberStatusLastChanged -= member.uniqueAddress

    case MemberLeft(member) =>
      memberStatusLastChanged -= member.uniqueAddress

    case MemberExited(member) =>
      memberStatusLastChanged -= member.uniqueAddress

    case MemberRemoved(member, _) =>
      memberStatusLastChanged -= member.uniqueAddress

    // reachability events
    case UnreachableMember(member) =>
      log.debug("Unreachable member {}", member)
      memberStatusLastChanged += (member.uniqueAddress -> Deadline.now.+(stableAfterPeriod))
      log.debug("Members: {}", memberStatusLastChanged)

    case ReachableMember(member) =>
      log.debug("Reachable member {}", member)
      memberStatusLastChanged -= member.uniqueAddress
      log.debug("Members: {}", memberStatusLastChanged)

    case ActOnSbrDecision =>
      strategy.sbrDecision(ClusterHelper(cluster, memberStatusLastChanged))

    case _ => () // do nothing for other messages
  }
}
