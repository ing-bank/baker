package com.ing.baker.runtime.actor.downing

import akka.cluster.MultiNodeClusterSpec
import akka.remote.testconductor.RoleName
import akka.remote.testkit.{MultiNodeSpec, STMultiNodeSpec}
import akka.remote.transport.ThrottlerTransportAdapter.Direction.Both
import akka.testkit.{ImplicitSender, LongRunningTest}

import scala.concurrent.duration.DurationInt
import scala.concurrent.duration._

class SplitBrainResolverHickUpNodeSpecMultiJvmNodeA extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false, downRemovalMargin = 10 seconds))
class SplitBrainResolverHickUpNodeSpecMultiJvmNodeB extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false, downRemovalMargin = 10 seconds))
class SplitBrainResolverHickUpNodeSpecMultiJvmNodeC extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false, downRemovalMargin = 10 seconds))
class SplitBrainResolverHickUpNodeSpecMultiJvmNodeD extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false, downRemovalMargin = 10 seconds))
class SplitBrainResolverHickUpNodeSpecMultiJvmNodeE extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = false, downRemovalMargin = 10 seconds))

abstract class SplitBrainResolverHickUpNodeSpec(splitBrainResolverConfig: SplitBrainResolverConfig) extends MultiNodeSpec(splitBrainResolverConfig)
  with STMultiNodeSpec with ImplicitSender with MultiNodeClusterSpec {

  import splitBrainResolverConfig._

  muteMarkingAsUnreachable()

  "The majority leader in a 5 node cluster" must {

    val addressNodeD = address(nodeD)

    def hickUpOn(nodes: Seq[RoleName]): Unit = {
      log.info("Hick-up on")
      nodes.foreach {
        testConductor.blackhole(_, nodeE, Both).await
      }
    }

    def hickUpOff(nodes: Seq[RoleName]): Unit = {
      log.info("Hick-up off")
      nodes.foreach {
        testConductor.throttle(_, nodeE, Both, 100.0).await
      }
    }

    "cluster should be up" taggedAs LongRunningTest in {
      awaitClusterUp(nodeA, nodeB, nodeC, nodeD, nodeE)
      enterBarrier("cluster-is-up")
    }

    "remove node even when another node is causing a hick-up" taggedAs LongRunningTest in {
      import system.dispatcher

      val onTask = system.scheduler.schedule(0 seconds, 2 seconds, () => {
        runOn(nodeA) {
          hickUpOn(Seq(nodeA, nodeB, nodeC))
        }
      })
      val offTask = system.scheduler.schedule(1 seconds, 2 seconds, () => {
        runOn(nodeA) {
          hickUpOff(Seq(nodeA, nodeB, nodeC))
        }
      })
      val blackholeNodeDTask = system.scheduler.scheduleOnce(8 seconds, () => {
        log.info("Making nodeD unreachable")
        runOn(nodeA) {
          Seq(nodeA, nodeB, nodeC, nodeE).foreach {
            testConductor.blackhole(_, nodeD, Both).await
          }
        }
      })

      awaitMembersUp(numberOfMembers = 5, canNotBePartOfMemberRing = Set(), 5 seconds)
      enterBarrier("all-members-should-still-be-up")

      Thread.sleep(20 * 1000)
      // NodeD should not be part of the cluster
      runOn(nodeA, nodeB, nodeC, nodeE) {
        awaitMembersUp(numberOfMembers = 4, canNotBePartOfMemberRing = Set(addressNodeD), 10 seconds)
        enterBarrier("node-d-should-have-left")
      }

      runOn(nodeD) {
        awaitAssert(
          clusterView.isTerminated should be(true),
          20 seconds,
          1 second
        )
        enterBarrier("node-d-should-have-left")
      }

      // Cleanup the tasks
      Seq(onTask, offTask, blackholeNodeDTask).foreach(_.cancel)
    }
  }
}
