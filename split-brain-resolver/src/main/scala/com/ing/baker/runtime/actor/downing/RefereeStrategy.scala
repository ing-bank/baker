package com.ing.baker.runtime.actor.downing

import akka.actor.Address
import org.slf4j.LoggerFactory

class RefereeStrategy(refereeAddress: Address, downAllIfLessThanNodes: Int) extends Strategy {

  private val log = LoggerFactory.getLogger(classOf[RefereeStrategy])

  override def sbrDecision(clusterHelper: ClusterHelper): Unit = {
    if (isRefereeUnreachable(clusterHelper)) {
      log.info(s"SplitBrainResolver RefereeStrategy: ${clusterHelper.myUniqueAddress}. Can not see referee. Downing myself")
      clusterHelper.downSelf()
    } else if (amIReferee(clusterHelper)) {
      if (notEnoughReachableNodes(clusterHelper)) {
        log.info(s"SplitBrainResolver RefereeStrategy: ${clusterHelper.myUniqueAddress}. I'm referee. Not enough nodes in the cluster. Downing all nodes}")
        clusterHelper.members
          .map(_.address)
          .foreach(clusterHelper.down)
      } else if (areThereUnreachableNodes(clusterHelper)) {
        log.info(s"SplitBrainResolver RefereeStrategy: ${clusterHelper.myUniqueAddress}. I'm referee. Downing these nodes: ${clusterHelper.unreachables}")
        clusterHelper.unreachables
          .map(_.address)
          .foreach(clusterHelper.down)
      }
    }
  }

  private def isRefereeUnreachable(clusterHelper: ClusterHelper): Boolean =
    clusterHelper.unreachables.map(_.address) contains refereeAddress

  private def amIReferee(clusterHelper: ClusterHelper): Boolean =
    clusterHelper.myUniqueAddress.address == refereeAddress

  private def notEnoughReachableNodes(clusterHelper: ClusterHelper): Boolean =
    clusterHelper.reachables.size >= downAllIfLessThanNodes

  private def areThereUnreachableNodes(clusterHelper: ClusterHelper): Boolean =
    clusterHelper.unreachables.nonEmpty
}
