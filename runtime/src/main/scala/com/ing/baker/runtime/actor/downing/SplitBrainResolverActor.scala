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
//  var allNodes: SortedSet[UniqueAddress] = allMembers.map(m => m.uniqueAddress)

  private def unreachableMembers(): Set[Member] = allMembers.filter(m => unreachableNodes contains m.uniqueAddress)
  private def reachableNodes(): Set[UniqueAddress] = allMembers.filterNot(m => unreachableNodes contains m.uniqueAddress).map(m => m.uniqueAddress)
  private def isMember: Boolean = allMembers.exists(_.uniqueAddress == cluster.selfUniqueAddress)
  private def oldestNode: UniqueAddress = allMembers.head.uniqueAddress // first member is the oldest in this sorted set

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

  /*
    macro SbrDecision() {
      if (IsMember(self) /\ IsLeader(self) /\ Cardinality(unreachableNodes[self]) > 0) {
        with (nodesToDown = NodesToDown(self)) {
          debug[self] := <<"sbr decision. nodesToDown=", nodesToDown>>;

          if (Contains(nodesToDown, self)) {
            \* leader going down
            members[self] := {};
            unreachableNodes[self] := {};

            \* mark this node as dead so it does not come back again
            deadNodes := deadNodes \cup {self};

            \* choose another node as oldest node if I am the oldest and going down.
            if(oldestNode = self) {
              oldestNode := ChooseOne(Nodes \ {self});
            }
          } else {
            members[self] := members[self] \ nodesToDown;
            unreachableNodes[self] := unreachableNodes[self] \ nodesToDown;
          }
        }
      }
    }

    NodesToDown(n) ==
      IF Cardinality(members[n]) = 0
      THEN Nodes \* Down all known nodes since I am not a member and I do not know any members
      ELSE IF Cardinality(unreachableNodes[n]) * 2 = Cardinality(members[n]) \* cannot decide minority or majority? equal size?
           THEN IF Contains(unreachableNodes[n], oldestNode) \* Check if the oldest node is unreachable, and let the group with oldest member survives
                THEN Reachables(n) \* down reachables
                ELSE unreachableNodes[n] \* down unreachableNodes
           ELSE IF Cardinality(unreachableNodes[n]) * 2 < Cardinality(members[n]) \* am I in majority?
                THEN unreachableNodes[n] \* down unreachableNodes
                ELSE Reachables(n) \* down reachables

   */
  private def sbrDecision(): Unit = {

    if (isMember && isLeader && unreachableNodes.nonEmpty) {
      val nodesToDown = this.nodesToDown()
      log.info("{} downing these nodes {}", cluster.selfAddress, nodesToDown)
      if (nodesToDown contains cluster.selfUniqueAddress) {
        // leader going down
        cluster.leave(cluster.selfAddress)
      } else {
        nodesToDown.foreach(a => cluster.leave(a.address))
      }
    }
  }

  private def nodesToDown(): Set[UniqueAddress] = {
    val unreachableMemberSize = unreachableMembers().size
    if (unreachableMemberSize * 2 == allMembers.size) { // cannot decide minority or majority? equal size?
      if (unreachableNodes contains oldestNode) {
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
