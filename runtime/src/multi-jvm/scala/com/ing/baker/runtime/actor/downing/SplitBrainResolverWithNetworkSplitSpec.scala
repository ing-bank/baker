package com.ing.baker.runtime.actor.downing

import akka.cluster.MultiNodeClusterSpec
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
        testConductor.blackhole(nodeA, nodeE, Both).await
        testConductor.blackhole(nodeB, nodeE, Both).await
        testConductor.blackhole(nodeC, nodeE, Both).await
        testConductor.blackhole(nodeD, nodeE, Both).await

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
        testConductor.blackhole(nodeA, nodeB, Both).await
        testConductor.blackhole(nodeC, nodeB, Both).await
        testConductor.blackhole(nodeD, nodeB, Both).await

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

    "DOWN itself when in minority" taggedAs LongRunningTest in {
      val firstAddress = address(nodeA)

      enterBarrier("before-unreachable-first-node")
      runOn(nodeA) {
        // drop all messages from/to 'first' node
        testConductor.blackhole(nodeA, nodeC, Both).await
        testConductor.blackhole(nodeA, nodeD, Both).await

        enterBarrier("unreachable-first-node")

        awaitAssert(
          clusterView.isTerminated should be(true),
          20 seconds,
          1 second
        )
      }

      runOn(nodeC, nodeD) {
        enterBarrier("unreachable-first-node")

        awaitMembersUp(numberOfMembers = 2, canNotBePartOfMemberRing = Set(firstAddress), 30 seconds)
      }

      runOn(nodeB, nodeE) {
        enterBarrier("unreachable-first-node")
      }

      enterBarrier("await-completion-3")
    }

  }
}