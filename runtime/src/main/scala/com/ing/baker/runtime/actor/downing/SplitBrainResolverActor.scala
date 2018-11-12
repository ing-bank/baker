package com.ing.baker.runtime.actor.downing

import akka.actor.{Actor, Cancellable, Props}
import akka.cluster.ClusterEvent._
import akka.cluster._
import akka.event.{DiagnosticLoggingAdapter, Logging}
import com.ing.baker.runtime.actor.downing.SplitBrainResolverActor.ActOnSbrDecision

import scala.collection.immutable.SortedSet
import scala.concurrent.duration.FiniteDuration

private[downing] object SplitBrainResolverActor {
  def props(downRemovalMargin: FiniteDuration) = Props(classOf[SplitBrainResolverActor], downRemovalMargin)

  case object ActOnSbrDecision
}

private[downing] class SplitBrainResolverActor(downRemovalMargin: FiniteDuration) extends Actor {

  val log: DiagnosticLoggingAdapter = Logging.getLogger(this)

  var isLeader = false

  var allMembers: SortedSet[Member] = SortedSet.empty(Member.ordering)
  var unreachableNodes: Set[UniqueAddress] = Set.empty[UniqueAddress]

  private def unreachableMembers(): Set[Member] = allMembers.filter(m => unreachableNodes contains m.uniqueAddress)
  private def reachableNodes(): Set[UniqueAddress] = allMembers.filterNot(m => unreachableNodes contains m.uniqueAddress).map(m => m.uniqueAddress)
  private def isMember: Boolean = allMembers.exists(_.uniqueAddress == cluster.selfUniqueAddress)
  private def nodeWithSmallestAddress: UniqueAddress = allMembers.head.uniqueAddress // first member is the oldest in this sorted set

  private def replaceMember(member: Member): Unit = {
    allMembers -= member
    allMembers += member
  }

  import context.dispatcher
  val actOnSbrDecisionTask: Cancellable = context.system.scheduler.schedule(downRemovalMargin, downRemovalMargin, self, ActOnSbrDecision)

  val cluster = Cluster(context.system)

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

    // Initial Cluster State is received in the beginning for once
    case clusterState: CurrentClusterState =>
      isLeader = clusterState.leader contains cluster.selfAddress
      allMembers = clusterState.members.filterNot(m => m.status == MemberStatus.Removed)

    // member events
    case MemberUp(member) =>
      log.info("Member up {}", member)
      replaceMember(member)

    case MemberLeft(member) =>
      log.info("Member left {}", member)
      replaceMember(member)

    case MemberExited(member) =>
      log.info("Member exited {}", member)
      replaceMember(member)

    case MemberRemoved(member, previousStatus) =>
      log.info("Member removed {}, previous status {}", member, previousStatus)
      allMembers -= member

    // cluster domain events
    case LeaderChanged(newLeader) =>
      log.info("Leader changed to {}", newLeader)
      isLeader = newLeader contains cluster.selfAddress
      // TODO test if this (acting immediately) doesn't break some corner case scenarios
      if (isLeader) sbrDecision()

    // reachability events
    case UnreachableMember(member) =>
      log.info("Unreachable member {}", member)
      replaceMember(member)
      if (!Set[MemberStatus](MemberStatus.Down, MemberStatus.Exiting).contains(member.status))
        unreachableNodes += member.uniqueAddress

    case ReachableMember(member) =>
      log.info("Reachable member {}", member)
      replaceMember(member)
      unreachableNodes -= member.uniqueAddress

    case ActOnSbrDecision =>
      log.info("act on sbr decision. self: {} isLeader: {}", cluster.selfAddress, isLeader)
      sbrDecision()

    case _ => () // do nothing for other messages

  }

  private def sbrDecision(): Unit = {


    if (isMember && isLeader && unreachableNodes.nonEmpty) {
      log.info(s"I am leader: Unreachables: $unreachableNodes")

      val nodesToDown = this.nodesToDown()
      log.info("{} downing these nodes {}", cluster.selfAddress, nodesToDown)
      if (nodesToDown contains cluster.selfUniqueAddress) {
        // leader going down
        cluster.down(cluster.selfAddress)
        log.info(s"Self node left cluster: ${cluster.selfAddress}")
      } else {
        nodesToDown.foreach(a => cluster.down(a.address))
        log.info(s"Nodes $nodesToDown left cluster")
      }
    } else {
      log.info(s"Not leader: Unreachables: $unreachableNodes")
    }
  }

  private def nodesToDown(): Set[UniqueAddress] = {
    val unreachableMemberSize = unreachableMembers().size
    if (unreachableMemberSize * 2 == allMembers.size) { // cannot decide minority or majority? equal size?
      if (unreachableNodes contains nodeWithSmallestAddress) {
        reachableNodes()
      } else {
        unreachableNodes
      }
    } else {
      if (unreachableMemberSize * 2 < allMembers.size) { // am I in majority?
        unreachableNodes
      } else {
        reachableNodes()
      }
    }
  }

}
