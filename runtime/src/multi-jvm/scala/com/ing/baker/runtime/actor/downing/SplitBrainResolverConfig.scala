package com.ing.baker.runtime.actor.downing

import akka.cluster.MultiNodeClusterSpec
import akka.remote.testkit.MultiNodeConfig
import com.typesafe.config.{Config, ConfigFactory}

final case class SplitBrainResolverConfig(useFailureDetectorPuppet: Boolean) extends MultiNodeConfig {

  val nodeA = role("nodeA")
  val nodeB = role("nodeB")
  val nodeC = role("nodeC")
  val nodeD = role("nodeD")
  val nodeE = role("nodeE")

  val bakerSplitBrainResolverConfig: Config = ConfigFactory.parseString(
    """
      |akka.cluster.downing-provider-class = com.ing.baker.runtime.actor.downing.SplitBrainResolver
      |baker.cluster.split-brain-resolver {
      |  down-removal-margin = 10 seconds
      |}
    """.stripMargin
  )

  val tanukkiSplitBrainResolverConfig: Config = ConfigFactory.parseString(
    """
      |akka.cluster.downing-provider-class = "tanukki.akka.cluster.autodown.MajorityLeaderAutoDowning"
      |custom-downing {
      |  stable-after = 10s
      |  majority-leader-auto-downing {
      |    majority-member-role = ""
      |    down-if-in-minority = true
      |    shutdown-actor-system-on-resolution = true
      |  }
      |}
    """.stripMargin
  )

  testTransport(on = true)

  commonConfig(ConfigFactory.parseString(
    """
      |akka.cluster.metrics.enabled=off
      |akka.actor.warn-about-java-serializer-usage = off
      |akka.remote.log-remote-lifecycle-events = off
      |akka.loglevel = INFO
    """.stripMargin)
    .withFallback(bakerSplitBrainResolverConfig)
//    .withFallback(tanukkiSplitBrainResolverConfig)
    .withFallback(MultiNodeClusterSpec.clusterConfig(useFailureDetectorPuppet))
  )

}
