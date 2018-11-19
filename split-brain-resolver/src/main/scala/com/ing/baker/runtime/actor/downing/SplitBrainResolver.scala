package com.ing.baker.runtime.actor.downing

import akka.ConfigurationException
import akka.actor.{ActorSystem, Props, AddressFromURIString}
import akka.cluster.DowningProvider
import net.ceedubs.ficus.Ficus._

import scala.concurrent.duration.{DurationDouble, FiniteDuration}

class SplitBrainResolver(actorSystem: ActorSystem) extends DowningProvider {
  private val config = actorSystem.settings.config

  override val downRemovalMargin: FiniteDuration = {
    val margin = config.as[FiniteDuration]("baker.cluster.split-brain-resolver.down-removal-margin")
    if (margin < 1.second) throw new IllegalArgumentException("Invalid config: baker.cluster.split-brain-resolver.down-removal-margin should be greater than 1 second")
    else margin
  }

  override def downingActorProps: Option[Props] = {
    val strategyName = config.getString("baker.cluster.split-brain-resolver.active-strategy")

    val strategy: Strategy = strategyName match {
      case "majority" =>
        new MajorityStrategy();

      case "referee" =>
        val refereeAddress = AddressFromURIString(config.getString("baker.cluster.split-brain-resolver.referee.address"))
        val downAllIfLessThanNodes = config.getInt("baker.cluster.split-brain-resolver.referee.down-all-if-less-than-nodes")
        new RefereeStrategy(refereeAddress, downAllIfLessThanNodes)

      case _ =>
        throw new ConfigurationException(s"Unknown split brain resolver strategy $strategyName")
    }

    Some(SplitBrainResolverActor.props(downRemovalMargin, strategy))
  }
}