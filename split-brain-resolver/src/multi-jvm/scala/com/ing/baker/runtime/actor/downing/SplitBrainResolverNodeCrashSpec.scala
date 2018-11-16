package com.ing.baker.runtime.actor.downing

import akka.cluster.MultiNodeClusterSpec
import akka.remote.testkit.{MultiNodeSpec, STMultiNodeSpec}
import akka.testkit.{ImplicitSender, LongRunningTest}

import scala.concurrent.duration.DurationInt

class SplitBrainResolverNodeCrashSpecMultiJvmNodeA extends SplitBrainResolverNodeCrashSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false))
class SplitBrainResolverNodeCrashSpecMultiJvmNodeB extends SplitBrainResolverNodeCrashSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false))
class SplitBrainResolverNodeCrashSpecMultiJvmNodeC extends SplitBrainResolverNodeCrashSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false))
class SplitBrainResolverNodeCrashSpecMultiJvmNodeD extends SplitBrainResolverNodeCrashSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false))
class SplitBrainResolverNodeCrashSpecMultiJvmNodeE extends SplitBrainResolverNodeCrashSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false))

abstract class SplitBrainResolverNodeCrashSpec(splitBrainResolverConfig: SplitBrainResolverConfig) extends MultiNodeSpec(splitBrainResolverConfig)
  with STMultiNodeSpec with ImplicitSender with MultiNodeClusterSpec {

  import splitBrainResolverConfig._

  muteMarkingAsUnreachable()

  "The majority leader in a 5 node cluster" must {

    "be able to DOWN a 'last' node that is UNREACHABLE" taggedAs LongRunningTest in {
      awaitClusterUp(nodeA, nodeB, nodeC, nodeD, nodeE)

      val fifthAddress = address(nodeE)

      enterBarrier("before-exit-fifth-node")

      runOn(nodeA) {
        // kill 'fifth' node
        testConductor.exit(nodeE, 0).await
        enterBarrier("down-fifth-node")

        // mark the node as unreachable in the failure detector
        markNodeAsUnavailable(fifthAddress)

        // --- HERE THE LEADER SHOULD DETECT FAILURE AND AUTO-DOWN THE UNREACHABLE NODE ---

        awaitMembersUp(numberOfMembers = 4, canNotBePartOfMemberRing = Set(fifthAddress), 30.seconds)
      }

      runOn(nodeE) {
        enterBarrier("down-fifth-node")
      }

      runOn(nodeB, nodeC, nodeD) {
        enterBarrier("down-fifth-node")

        awaitMembersUp(numberOfMembers = 4, canNotBePartOfMemberRing = Set(fifthAddress), 30.seconds)
      }

      enterBarrier("await-completion-1")
    }

    "be able to DOWN a 'middle' node that is UNREACHABLE" taggedAs LongRunningTest in {
      val secondAddress = address(nodeB)

      enterBarrier("before-exit-second-node")
      runOn(nodeA) {
        // kill 'second' node
        testConductor.exit(nodeB, 0).await
        enterBarrier("down-second-node")

        // mark the node as unreachable in the failure detector
        markNodeAsUnavailable(secondAddress)

        // --- HERE THE LEADER SHOULD DETECT FAILURE AND AUTO-DOWN THE UNREACHABLE NODE ---

        awaitMembersUp(numberOfMembers = 3, canNotBePartOfMemberRing = Set(secondAddress), 30.seconds)
      }

      runOn(nodeB) {
        enterBarrier("down-second-node")
      }

      runOn(nodeC, nodeD) {
        enterBarrier("down-second-node")

        awaitMembersUp(numberOfMembers = 3, canNotBePartOfMemberRing = Set(secondAddress), 30 seconds)
      }

      enterBarrier("await-completion-2")
    }

    "DOWN itself when in minority" taggedAs LongRunningTest in {
      val thirdAddress = address(nodeC)
      val fourthAddress = address(nodeD)

      enterBarrier("before-down-third-node")
      runOn(nodeA) {
        // kill 'third' node
        testConductor.exit(nodeC, 0).await
        testConductor.exit(nodeD, 0).await
        enterBarrier("down-third-node")

        // mark the node as unreachable in the failure detector
        markNodeAsUnavailable(thirdAddress)
        markNodeAsUnavailable(fourthAddress)

        awaitAssert(
          clusterView.isTerminated should be(true),
          20 seconds,
          1 second
        )
      }

      runOn(nodeC, nodeD) {
        enterBarrier("down-third-node")

        awaitAssert(
          clusterView.isTerminated should be(true),
          20 seconds,
          1 second
        )
      }

      runOn(nodeB, nodeC, nodeE) {
        enterBarrier("down-third-node")
      }

      enterBarrier("await-completion-3")
    }

  }
}