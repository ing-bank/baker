package com.ing.baker.runtime.actor.downing

import akka.cluster.UniqueAddress
import org.slf4j.LoggerFactory

class MajorityStrategy extends Strategy {

  private val log = LoggerFactory.getLogger(classOf[MajorityStrategy])

  override def sbrDecision(clusterHelper: ClusterHelper): Unit = {
    if (clusterHelper.amIMember && clusterHelper.amILeader && clusterHelper.unreachables.nonEmpty) {
      val nodesToDown = this.nodesToDown(clusterHelper)

      log.info(s"SplitBrainResolver: ${clusterHelper.myUniqueAddress} downing these nodes $nodesToDown")
      if (nodesToDown contains clusterHelper.myUniqueAddress) {
        // leader going down
        clusterHelper.downSelf()
      } else {
        nodesToDown.foreach(a => clusterHelper.down(a.address))
      }
    }
  }

  private def nodesToDown(clusterHelper: ClusterHelper): Set[UniqueAddress] = {
    val unreachableMemberSize = clusterHelper.unreachables.size
    if (unreachableMemberSize * 2 == clusterHelper.members.size) { // cannot decide minority or majority? equal size?
      if (clusterHelper.unreachableUniqueAddresses contains clusterHelper.nodeWithSmallestAddress.get) {
        clusterHelper.reachableUniqueAddresses.toSet
      } else {
        clusterHelper.unreachableUniqueAddresses
      }
    } else {
      if (unreachableMemberSize * 2 < clusterHelper.members.size) { // am I in majority?
        clusterHelper.unreachableUniqueAddresses
      } else {
        clusterHelper.reachableUniqueAddresses.toSet
      }
    }
  }
}
