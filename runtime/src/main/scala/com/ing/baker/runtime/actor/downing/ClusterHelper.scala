package com.ing.baker.runtime.actor.downing

import akka.actor.Address
import akka.cluster.{Cluster, Member, UniqueAddress}

import scala.collection.SortedSet
import scala.concurrent.duration.Deadline

case class ClusterHelper(cluster: Cluster, memberStatusLastChanged: Map[UniqueAddress, Deadline] ) {

  val memberStatusLastChangedReadable: Map[UniqueAddress, Long] = memberStatusLastChanged.map { case (address, deadline) =>
    address -> deadline.timeLeft.toSeconds
  }

  val unstableMembers: Set[UniqueAddress] = memberStatusLastChanged.filter(_._2.hasTimeLeft()).keys.toSet

  val members: SortedSet[Member] = cluster.state.members

  val unreachables: Set[Member] = cluster.state.unreachable.filterNot { member =>
    unstableMembers.contains(member.uniqueAddress)
  }

  val reachables: SortedSet[Member] = (members diff unreachables).filterNot { member =>
    unstableMembers.contains(member.uniqueAddress)
  }

  val reachableUniqueAddresses: SortedSet[UniqueAddress] = reachables.map(_.uniqueAddress)

  val unreachableUniqueAddresses: Set[UniqueAddress] = unreachables.map(_.uniqueAddress)

  val nodeWithSmallestAddress: Option[UniqueAddress] = members.headOption.map(_.uniqueAddress)

  val amIMember: Boolean = members.exists(_.uniqueAddress == cluster.selfUniqueAddress)

  val amILeader: Boolean = cluster.state.leader.contains(cluster.selfAddress)

  val myUniqueAddress: UniqueAddress = cluster.selfUniqueAddress

  def downSelf(): Unit =
    cluster.down(cluster.selfAddress)

  def down(address: Address): Unit =
    cluster.down(address)
}
