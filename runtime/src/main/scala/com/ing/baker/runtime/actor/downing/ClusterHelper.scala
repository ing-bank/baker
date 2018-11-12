package com.ing.baker.runtime.actor.downing

import akka.actor.Address
import akka.cluster.{Cluster, Member, MemberStatus, UniqueAddress}

import scala.collection.SortedSet

case class ClusterHelper(cluster: Cluster) {

  def members: SortedSet[Member] = cluster.state.members

  def unreachables: Set[Member] = cluster.state.unreachable

  def reachables: SortedSet[Member] = members diff unreachables

  def reachableUniqueAddresses: SortedSet[UniqueAddress] = reachables.map(_.uniqueAddress)

  def unreachableUniqueAddresses: Set[UniqueAddress] = unreachables.map(_.uniqueAddress)

  def nodeWithSmallestAddress: UniqueAddress = members.head.uniqueAddress

  def amIMember: Boolean = members.exists(_.uniqueAddress == cluster.selfUniqueAddress)

  def amILeader: Boolean = cluster.state.leader.contains(cluster.selfAddress)

  def downSelf(): Unit =
    cluster.down(cluster.selfAddress)

  def down(address: Address): Unit =
    cluster.down(address)

  def myUniqueAddress: UniqueAddress = cluster.selfUniqueAddress
}
