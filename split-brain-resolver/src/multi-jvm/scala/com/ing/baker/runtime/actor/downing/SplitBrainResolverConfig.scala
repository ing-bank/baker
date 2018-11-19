package com.ing.baker.runtime.actor.downing

import akka.cluster.MultiNodeClusterSpec
import akka.remote.testkit.MultiNodeConfig
import com.typesafe.config.{Config, ConfigFactory}

import scala.concurrent.duration.Duration
import scala.concurrent.duration._

sealed trait StrategyConfig
object MajorityStrategyConfig extends StrategyConfig
case class RefereeStrategyConfig(refereeAddress: String, downAllIfLessThanNodes: Int) extends StrategyConfig

final case class SplitBrainResolverConfig(useFailureDetectorPuppet: Boolean,
                                          downRemovalMargin: Duration = 2 seconds,
                                          strategyConfig: StrategyConfig
                                         )
  extends MultiNodeConfig {

  val nodeA = role("nodeA")
  val nodeB = role("nodeB")
  val nodeC = role("nodeC")
  val nodeD = role("nodeD")
  val nodeE = role("nodeE")

  testTransport(on = true)

  val strategyConfigString: String =
    strategyConfig match {
      case MajorityStrategyConfig =>
        s"""
           |baker.cluster.split-brain-resolver.active-strategy = "majority"
        """

      case RefereeStrategyConfig(refereeAddress, downAllIfLessThanNodes) =>
        s"""
           |baker.cluster.split-brain-resolver.active-strategy = "referee"
           |baker.cluster.split-brain-resolver.referee {
           |  address = $refereeAddress
           |  down-all-if-less-than-nodes = $downAllIfLessThanNodes
           |}
        """
    }

  val bakerSplitBrainResolverConfig: Config = ConfigFactory.parseString(
    s"""
      |akka.cluster.downing-provider-class = com.ing.baker.runtime.actor.downing.SplitBrainResolver
      |baker.cluster.split-brain-resolver {
      |  down-removal-margin = $downRemovalMargin
      |}
    """.stripMargin
  )

  commonConfig(ConfigFactory.parseString(
    """
      |akka.cluster.metrics.enabled=off
      |akka.actor.warn-about-java-serializer-usage = off
      |akka.remote.log-remote-lifecycle-events = off
      |akka.loglevel = INFO
    """.stripMargin)
    .withFallback(bakerSplitBrainResolverConfig)
    .withFallback(ConfigFactory.parseString(strategyConfigString.stripMargin))
    .withFallback(MultiNodeClusterSpec.clusterConfig(useFailureDetectorPuppet))
  )

  nodeConfig(nodeA) {
    ConfigFactory.parseString(
      """
        |akka.remote.netty.tcp.port = 49999
      """.stripMargin)
  }
}
