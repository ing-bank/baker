package com.ing.baker.runtime.actor.downing

import akka.actor.{Actor, Props}
import akka.cluster.ClusterEvent._
import akka.cluster.{Cluster, ClusterEvent, Member, MemberStatus}
import akka.event.{DiagnosticLoggingAdapter, Logging}
import com.ing.baker.runtime.actor.downing.SplitBrainResolverActor.ActOnSbrDecision

import scala.collection.immutable
import scala.concurrent.duration.FiniteDuration

private[downing] object SplitBrainResolverActor {
  def props(downRemovalMargin: FiniteDuration) = Props(classOf[SplitBrainResolverActor], downRemovalMargin)

  case object ActOnSbrDecision
}

private[downing] class SplitBrainResolverActor(downRemovalMargin: FiniteDuration) extends Actor {

  val log: DiagnosticLoggingAdapter = Logging.getLogger(this)

  val cluster = Cluster(context.system)

  private var isLeader = false
  private var members: immutable.SortedSet[Member] = immutable.SortedSet.empty(Member.ordering)
  private var unreachables: immutable.Set[Member] = immutable.Set.empty[Member]

  override def preStart(): Unit = {
    cluster.subscribe(self, ClusterEvent.InitialStateAsEvents, classOf[ClusterDomainEvent])
    super.preStart()
  }

  override def postStop(): Unit = {
    cluster.unsubscribe(self)
    //    tickTask.cancel()
    super.postStop()
  }

  override def receive: Receive = {

    // Initial Cluster State is received in the beginning for once
    case state: CurrentClusterState =>
      isLeader = state.leader contains cluster.selfAddress
      members = state.members.filterNot(_.status == MemberStatus.Removed)
      scheduleSbrDecision()
    //      members = immutable.SortedSet.empty(Member.ordering) union state.members.filterNot {m =>
    //        m.status == MemberStatus.Removed
    //      }

    // member events
    case MemberJoined(member) =>
      log.info("Member joined {}", member)

    case MemberWeaklyUp(member) =>
      log.info("Member weakly up {}", member)

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
      members -= member

    // cluster domain events
    case LeaderChanged(newLeader) =>
      log.info("Leader changed to {}", newLeader)
      isLeader = newLeader contains cluster.selfAddress

    case RoleLeaderChanged(role, newLeader) =>
      log.info("Role leader changed. Role {}, new leader {}", role, newLeader)

    case ClusterShuttingDown =>
      log.info("Cluster shutting down")

    // reachability events
    case UnreachableMember(member) =>
      log.info("Unreachable member {}", member)
      replaceMember(member)
      unreachables += member
      scheduleSbrDecision()

    case ReachableMember(member) =>
      log.info("Reachable member {}", member)
      replaceMember(member)
      unreachables -= member

    // data center reachability events
    case UnreachableDataCenter(dc) =>
      log.info("Unreachable data center {}", dc)

    case ReachableDataCenter(dc) =>
      log.info("Reachable data center {}", dc)

    case ActOnSbrDecision =>
      log.info("act on sbr decision")
      sbrDecision()

    case _ => () // do nothing for other messages

  }

  private def replaceMember(member: Member): Unit = {
    members -= member
    members += member
  }

  private def isMember: Boolean = members.exists(_.uniqueAddress == cluster.selfUniqueAddress)

  private def oldestMember: Member = members.head // first member is the oldest in this sorted set

  /*
    macro SbrDecision() {
      if (IsMember(self) /\ IsLeader(self) /\ Cardinality(unreachables[self]) > 0) {
        with (nodesToDown = NodesToDown(self)) {
          debug[self] := <<"sbr decision. nodesToDown=", nodesToDown>>;

          if (Contains(nodesToDown, self)) {
            \* leader going down
            members[self] := {};
            unreachables[self] := {};

            \* mark this node as dead so it does not come back again
            deadNodes := deadNodes \cup {self};

            \* choose another node as oldest node if I am the oldest and going down.
            if(oldestNode = self) {
              oldestNode := ChooseOne(Nodes \ {self});
            }
          } else {
            members[self] := members[self] \ nodesToDown;
            unreachables[self] := unreachables[self] \ nodesToDown;
          }
        }
      }
    }

    NodesToDown(n) ==
      IF Cardinality(members[n]) = 0
      THEN Nodes \* Down all known nodes since I am not a member and I do not know any members
      ELSE IF Cardinality(unreachables[n]) * 2 = Cardinality(members[n]) \* cannot decide minority or majority? equal size?
           THEN IF Contains(unreachables[n], oldestNode) \* Check if the oldest node is unreachable, and let the group with oldest member survives
                THEN Reachables(n) \* down reachables
                ELSE unreachables[n] \* down unreachables
           ELSE IF Cardinality(unreachables[n]) * 2 < Cardinality(members[n]) \* am I in majority?
                THEN unreachables[n] \* down unreachables
                ELSE Reachables(n) \* down reachables

   */
  private def sbrDecision(): Unit = {

    if (isMember && isLeader && unreachables.nonEmpty) {
      val nodesToDown = this.nodesToDown()
      log.info("{} downing these nodes {}", cluster.selfUniqueAddress, nodesToDown)
      if (nodesToDown.exists(_.uniqueAddress == cluster.selfUniqueAddress)) {
        // leader going down
        cluster.leave(cluster.selfAddress)
      } else {
        nodesToDown.foreach(m => cluster.leave(m.uniqueAddress.address))
      }
    }
  }

  private def nodesToDown(): Set[Member] = {
    if (unreachables.size * 2 == members.size) { // cannot decide minority or majority? equal size?
      if (unreachables contains oldestMember) {
        members diff unreachables // down reachables
      } else {
        unreachables // down unreachables
      }
    } else {
      if (unreachables.size * 2 < members.size) { // am I in majority?
        unreachables // down unreachables
      } else {
        members diff unreachables // down reachables
      }
    }
  }

  private def scheduleSbrDecision(): Unit = {
    import context.dispatcher
    context.system.scheduler.scheduleOnce(downRemovalMargin, self, ActOnSbrDecision)
  }

}
