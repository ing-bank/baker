package com.ing.baker.runtime.actor.downing

import akka.actor.{ActorSystem, Props}
import akka.cluster.DowningProvider
import net.ceedubs.ficus.Ficus._

import scala.concurrent.duration.{DurationDouble, FiniteDuration}

class SplitBrainResolver(actorSystem: ActorSystem) extends DowningProvider {

  override val downRemovalMargin: FiniteDuration = {
    val margin = actorSystem.settings.config.as[FiniteDuration]("baker.cluster.split-brain-resolver.down-removal-margin")
    if (margin < 1.second) throw new IllegalArgumentException("Invalid config: baker.cluster.split-brain-resolver.down-removal-margin should be greater than 1 second")
    else margin
  }

  override def downingActorProps: Option[Props] = Some(SplitBrainResolverActor.props(downRemovalMargin))
}
