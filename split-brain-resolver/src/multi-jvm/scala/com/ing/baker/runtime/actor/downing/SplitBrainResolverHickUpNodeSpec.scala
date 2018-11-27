package com.ing.baker.runtime.actor.downing

import akka.actor.Cancellable
import akka.cluster.MultiNodeClusterSpec
import akka.remote.testkit.{MultiNodeSpec, STMultiNodeSpec}
import akka.testkit.{ImplicitSender, LongRunningTest}

import scala.concurrent.duration.DurationInt

class SplitBrainResolverHickUpNodeSpecMultiJvmNodeA extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = true, stableAfterPeriod = 7 seconds))
class SplitBrainResolverHickUpNodeSpecMultiJvmNodeB extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = true, stableAfterPeriod = 7 seconds))
class SplitBrainResolverHickUpNodeSpecMultiJvmNodeC extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = true, stableAfterPeriod = 7 seconds))
class SplitBrainResolverHickUpNodeSpecMultiJvmNodeD extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = true, stableAfterPeriod = 7 seconds))
class SplitBrainResolverHickUpNodeSpecMultiJvmNodeE extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = true, stableAfterPeriod = 7 seconds))

abstract class SplitBrainResolverHickUpNodeSpec(splitBrainResolverConfig: SplitBrainResolverConfig) extends MultiNodeSpec(splitBrainResolverConfig)
  with STMultiNodeSpec with ImplicitSender with MultiNodeClusterSpec {

  import splitBrainResolverConfig._

  muteMarkingAsUnreachable()

  import system.dispatcher

  var scheduleReachable: Option[Cancellable] = None
  var scheduleUnreachable: Option[Cancellable] = None

  val addressNodeD = address(nodeD)
  val addressNodeE = address(nodeE)

  def statusNodeE(reachable: Boolean): Unit = {
    if (reachable) {
        markNodeAsAvailable(addressNodeE)
      log.info("NodeE reachable")
    } else {
        markNodeAsUnavailable(addressNodeE)
      log.info("NodeE UNreachable")
    }
  }

  "The majority leader in a 5 node cluster" must {

    "cluster should be up" taggedAs LongRunningTest in {
      awaitClusterUp(nodeA, nodeB, nodeC, nodeD, nodeE)
      enterBarrier("cluster-is-up")

      runOn(nodeA) {
        scheduleReachable = Some(system.scheduler.schedule(0 seconds, 2 second, () => statusNodeE(reachable = true)))
        scheduleUnreachable = Some(system.scheduler.schedule(1 seconds, 2 second, () => statusNodeE(reachable = false)))
      }

      Thread.sleep(10 * 1000)
      enterBarrier("waited-for-10-seconds")

      runOn(nodeA, nodeB, nodeC, nodeD) {
        log.info("10 seconds passed, checking for cluster state")
        awaitMembersUp(numberOfMembers = 5, canNotBePartOfMemberRing = Set.empty, 2 seconds)
      }
    }

    "majority should down one unreachable node (nodeD) but not the unstable(flickering) node (nodeE)" taggedAs LongRunningTest in {
      runOn(nodeA) {
        markNodeAsUnavailable(addressNodeD)
      }

      runOn(nodeD) {
        awaitAssert(
          clusterView.isTerminated should be(true),
          20 seconds,
          1 second
        )
        enterBarrier("fourth-node-down")
      }

      runOn(nodeA, nodeB, nodeC) {
        awaitMembersUp(numberOfMembers = 4, canNotBePartOfMemberRing = Set(addressNodeD), 20 seconds)
        enterBarrier("fourth-node-down")
      }

      runOn(nodeA) {
        statusNodeE(reachable = true)
      }

      runOn(nodeE) {
        awaitMembersUp(numberOfMembers = 4, canNotBePartOfMemberRing = Set(addressNodeD), 20 seconds)
        enterBarrier("fourth-node-down")
      }

    }

    "cleanup" in {
      scheduleReachable.foreach(_.cancel())
      scheduleUnreachable.foreach(_.cancel())
    }

  }
}
