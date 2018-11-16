package com.ing.baker.runtime.actor.downing

import akka.actor.Address
import akka.cluster.MultiNodeClusterSpec
import akka.remote.testconductor.RoleName
import akka.remote.testkit.{MultiNodeSpec, STMultiNodeSpec}
import akka.remote.transport.ThrottlerTransportAdapter.Direction.Both
import akka.testkit.{ImplicitSender, LongRunningTest}

import scala.concurrent.duration.DurationInt

class SplitBrainResolverWithNetworkSplitSpecMultiJvmNodeA extends SplitBrainResolverWithNetworkSplitSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false))
class SplitBrainResolverWithNetworkSplitSpecMultiJvmNodeB extends SplitBrainResolverWithNetworkSplitSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false))
class SplitBrainResolverWithNetworkSplitSpecMultiJvmNodeC extends SplitBrainResolverWithNetworkSplitSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false))
class SplitBrainResolverWithNetworkSplitSpecMultiJvmNodeD extends SplitBrainResolverWithNetworkSplitSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false))
class SplitBrainResolverWithNetworkSplitSpecMultiJvmNodeE extends SplitBrainResolverWithNetworkSplitSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false))

abstract class SplitBrainResolverWithNetworkSplitSpec(splitBrainResolverConfig: SplitBrainResolverConfig) extends MultiNodeSpec(splitBrainResolverConfig)
  with STMultiNodeSpec with ImplicitSender with MultiNodeClusterSpec {

  import splitBrainResolverConfig._

  muteMarkingAsUnreachable()

  "The majority leader in a 5 node cluster" must {

    "be able to DOWN a 'last' node that is UNREACHABLE" taggedAs LongRunningTest in {
      awaitClusterUp(nodeA, nodeB, nodeC, nodeD, nodeE)

      val fifthAddress = address(nodeE)

      enterBarrier("before-unreachable-fifth-node")

      runOn(nodeA) {
        // drop all messages from/to 'fifth' node
        Set(nodeA, nodeB, nodeC, nodeD)
          .map(testConductor.blackhole(_, nodeE, Both))
          .foreach(_.await)

        enterBarrier("unreachable-fifth-node")

        // --- HERE THE LEADER SHOULD DETECT FAILURE AND AUTO-DOWN THE UNREACHABLE NODE ---

        awaitMembersUp(numberOfMembers = 4, canNotBePartOfMemberRing = Set(fifthAddress), 30.seconds)
      }

      runOn(nodeE) {
        enterBarrier("unreachable-fifth-node")
        awaitAssert(
          clusterView.isTerminated should be(true),
          20 seconds,
          1 second
        )

      }

      runOn(nodeB, nodeC, nodeD) {
        enterBarrier("unreachable-fifth-node")

        awaitMembersUp(numberOfMembers = 4, canNotBePartOfMemberRing = Set(fifthAddress), 30.seconds)
      }

      enterBarrier("await-completion-1")
    }

    "be able to DOWN a 'middle' node that is UNREACHABLE" taggedAs LongRunningTest in {
      val secondAddress = address(nodeB)

      enterBarrier("before-unreachable-second-node")
      runOn(nodeA) {
        // drop all messages to/from 'second' node
        Set(nodeA, nodeC, nodeD)
          .map(testConductor.blackhole(_, nodeB, Both))
          .foreach(_.await)

        enterBarrier("unreachable-second-node")

        // --- HERE THE LEADER SHOULD DETECT FAILURE AND AUTO-DOWN THE UNREACHABLE NODE ---

        awaitMembersUp(numberOfMembers = 3, canNotBePartOfMemberRing = Set(secondAddress), 30.seconds)
      }

      runOn(nodeB) {
        enterBarrier("unreachable-second-node")
        awaitAssert(
          clusterView.isTerminated should be(true),
          20 seconds,
          1 second
        )
      }

      runOn(nodeC, nodeD) {
        enterBarrier("unreachable-second-node")

        awaitMembersUp(numberOfMembers = 3, canNotBePartOfMemberRing = Set(secondAddress), 30 seconds)
      }

      runOn(nodeE) {
        enterBarrier("unreachable-second-node")

      }

      enterBarrier("await-completion-2")
    }

    "DOWN itself (first node) when in minority" taggedAs LongRunningTest in {
      val fourthAddress = address(nodeD)

      enterBarrier("before-unreachable-fourth-node")
      runOn(nodeA) {
        // drop all messages from/to 'fourth' node
        Set(nodeA, nodeC)
          .map(testConductor.blackhole(_, nodeD, Both))
          .foreach(_.await)
      }

      runOn(nodeA, nodeC) {
        enterBarrier("unreachable-fourth-node")

        awaitMembersUp(numberOfMembers = 2, canNotBePartOfMemberRing = Set(fourthAddress), 30 seconds)
      }

      runOn(nodeD) {
        awaitAssert(
          clusterView.isTerminated should be(true),
          20 seconds,
          1 second
        )
        enterBarrier("unreachable-fourth-node")
      }

      runOn(nodeB, nodeE) {
        enterBarrier("unreachable-fourth-node")
      }

      enterBarrier("await-completion-3")
    }

    "In equal split DOWN the .... side" taggedAs LongRunningTest in {
      // At this point, only A and C are alive
      val all: Seq[(Address, RoleName)] = Seq(nodeA, nodeC).map(n => (address(n), n))
      val (_, oldestNode) = all.min
      val (toDownAddress, toDownNode) = all.max

      enterBarrier("before-equal-split")
      runOn(nodeA) {
        testConductor.blackhole(nodeA, nodeC, Both).await
      }

      runOn(oldestNode) {
        enterBarrier("split-between-remaining-nodes")

        // Test that A survives the split
        awaitMembersUp(numberOfMembers = 1, canNotBePartOfMemberRing = Set(toDownAddress), 30 seconds)
      }

      runOn(toDownNode) {
        awaitAssert(
          clusterView.isTerminated should be(true),
          20 seconds,
          1 second
        )
        enterBarrier("split-between-remaining-nodes")
      }

      runOn(nodeB, nodeD, nodeE) {
        enterBarrier("split-between-remaining-nodes")
      }

      enterBarrier("await-completion-4")
    }
  }
}