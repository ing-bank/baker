package com.ing.baker.runtime.actor.downing

import akka.actor.Address
import akka.cluster.{Cluster, ClusterEvent, Member, UniqueAddress}

import scala.collection.SortedSet
import scala.concurrent.duration.Deadline

case class ClusterHelper(cluster: Cluster, memberStatusLastChanged: Map[UniqueAddress, Deadline]) {

  // Take a snapshot of the cluster state
  private val clusterState: ClusterEvent.CurrentClusterState = cluster.state

  val members: SortedSet[Member] = clusterState.members

  val unstableMembersUniqueAddresses: Set[UniqueAddress] = memberStatusLastChanged.filter(_._2.hasTimeLeft()).keys.toSet

  val unreachables: Set[Member] = clusterState.unreachable.filterNot { member =>
    unstableMembersUniqueAddresses.contains(member.uniqueAddress)
  }

  val reachables: SortedSet[Member] = (members diff unreachables).filterNot { member =>
    unstableMembersUniqueAddresses.contains(member.uniqueAddress)
  }

  val reachableUniqueAddresses: SortedSet[UniqueAddress] = reachables.map(_.uniqueAddress)

  val unreachableUniqueAddresses: Set[UniqueAddress] = unreachables.map(_.uniqueAddress)

  val nodeWithSmallestAddress: Option[UniqueAddress] = members.headOption.map(_.uniqueAddress)

  val amIMember: Boolean = members.exists(_.uniqueAddress == cluster.selfUniqueAddress)

  val amILeader: Boolean = clusterState.leader.contains(cluster.selfAddress)

  val myUniqueAddress: UniqueAddress = cluster.selfUniqueAddress

  def downSelf(): Unit =
    cluster.down(cluster.selfAddress)

  def down(address: Address): Unit =
    cluster.down(address)
}
