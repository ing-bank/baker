package com.ing.baker.runtime.actor.downing

import akka.cluster.MultiNodeClusterSpec
import akka.remote.testkit.MultiNodeConfig
import com.typesafe.config.ConfigFactory

final case class SplitBrainResolverConfig() extends MultiNodeConfig {

  val nodeA = role("nodeA")
  val nodeB = role("nodeB")
  val nodeC = role("nodeC")
  val nodeD = role("nodeD")
  val nodeE = role("nodeE")

  commonConfig(ConfigFactory.parseString(
    """
      |akka.cluster.downing-provider-class = com.ing.baker.runtime.actor.downing.SplitBrainResolver
      |baker.cluster.split-brain-resolver {
      |  down-removal-margin = 10 seconds
      |}
      |akka.cluster.metrics.enabled=off
      |akka.actor.warn-about-java-serializer-usage = off
      |akka.remote.log-remote-lifecycle-events = off
      |akka.loglevel = INFO
    """.stripMargin)
    .withFallback(MultiNodeClusterSpec.clusterConfig(true))
  )

//  nodeConfig(nodeA, nodeB, nodeC, nodeD, nodeE)(ConfigFactory.parseString(
//    """
//      |akka.cluster {
//      |  roles = [role]
//      |}
//    """.stripMargin))

}
