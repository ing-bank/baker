package com.ing.baker.runtime.actor.downing

import akka.actor.Cancellable
import akka.cluster.MultiNodeClusterSpec
import akka.remote.testconductor.RoleName
import akka.remote.testkit.{MultiNodeSpec, STMultiNodeSpec}
import akka.remote.transport.ThrottlerTransportAdapter.Direction.Both
import akka.testkit.{ImplicitSender, LongRunningTest}

import scala.annotation.tailrec
import scala.concurrent.duration.DurationInt
import scala.concurrent.duration._

class SplitBrainResolverHickUpNodeSpecMultiJvmNodeA extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = true, downRemovalMargin = 5 seconds))
class SplitBrainResolverHickUpNodeSpecMultiJvmNodeB extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = true, downRemovalMargin = 5 seconds))
class SplitBrainResolverHickUpNodeSpecMultiJvmNodeC extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = true, downRemovalMargin = 5 seconds))
class SplitBrainResolverHickUpNodeSpecMultiJvmNodeD extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = true, downRemovalMargin = 5 seconds))
class SplitBrainResolverHickUpNodeSpecMultiJvmNodeE extends SplitBrainResolverHickUpNodeSpec(SplitBrainResolverConfig(useFailureDetectorPuppet = true, downRemovalMargin = 5 seconds))

abstract class SplitBrainResolverHickUpNodeSpec(splitBrainResolverConfig: SplitBrainResolverConfig) extends MultiNodeSpec(splitBrainResolverConfig)
  with STMultiNodeSpec with ImplicitSender with MultiNodeClusterSpec {

  import splitBrainResolverConfig._

  muteMarkingAsUnreachable()

  import system.dispatcher
  var task: Option[Cancellable] = None

  val addressNodeD = address(nodeD)
  val addressNodeE = address(nodeE)

  def hickUpOn(): Unit = {
    log.info("Hick on")
//    testConductor.blackhole(nodeA, nodeE, Both).await
//    testConductor.blackhole(nodeB, nodeE, Both).await
//    testConductor.blackhole(nodeC, nodeE, Both).await
    markNodeAsUnavailable(addressNodeE)
  }

  def hickUpOff(): Unit = {
    log.info("Hick off")
//    testConductor.throttle(nodeA, nodeE, Both, Double.MaxValue).await
//    testConductor.throttle(nodeB, nodeE, Both, Double.MaxValue).await
//    testConductor.throttle(nodeC, nodeE, Both, Double.MaxValue).await
    markNodeAsAvailable(addressNodeE)
  }

  def doOn(): Cancellable =  {
    system.scheduler.scheduleOnce(2 seconds, () => {
      hickUpOn()
      task = Option(doOff())
    })
  }

  def doOff(): Cancellable = {
    system.scheduler.scheduleOnce(2 seconds, () => {
      hickUpOff()
      task = Option(doOn())
    })
  }

  "The majority leader in a 5 node cluster" must {

    "cluster should be up" taggedAs LongRunningTest in {
      awaitClusterUp(nodeA, nodeB, nodeC, nodeD, nodeE)
      enterBarrier("cluster-is-up")
    }

    "remove node even when another node is causing a hick-up" taggedAs LongRunningTest in {
      val blackholeNodeDTask = system.scheduler.scheduleOnce(8 seconds, () => {
        runOn(nodeA) {
          log.info("Making nodeD unreachable")
//          testConductor.blackhole(nodeA, nodeD, Both).await
//          testConductor.blackhole(nodeB, nodeD, Both).await
//          testConductor.blackhole(nodeC, nodeD, Both).await
//          testConductor.blackhole(nodeE, nodeD, Both).await
          markNodeAsUnavailable(addressNodeD)
        }
      })

      runOn(nodeA) {
        task = Some(doOff())
      }

      runOn(nodeD) {
        awaitAssert(
          clusterView.isTerminated should be(true),
          60 seconds,
          1 second
        )
        enterBarrier("unreachable-fourth-node")
      }

      // NodeD should not be part of the cluster
      runOn(nodeA, nodeB, nodeC, nodeE) {
        awaitMembersUp(numberOfMembers = 4, canNotBePartOfMemberRing = Set(addressNodeD), 60 seconds)
        enterBarrier("unreachable-fourth-node")
      }

      enterBarrier("finish-before-cleanup")

      // Cleanup the tasks
      task.foreach(_.cancel)
      blackholeNodeDTask.cancel()
    }
  }
}
