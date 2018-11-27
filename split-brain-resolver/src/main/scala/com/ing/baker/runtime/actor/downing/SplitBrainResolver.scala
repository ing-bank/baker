package com.ing.baker.runtime.actor.downing

import akka.actor.{ActorSystem, Props}
import akka.cluster.DowningProvider
import net.ceedubs.ficus.Ficus._

import scala.concurrent.duration.{DurationDouble, FiniteDuration}

class SplitBrainResolver(actorSystem: ActorSystem) extends DowningProvider {

  override val downRemovalMargin: FiniteDuration = {
    val stableAfter = actorSystem.settings.config.as[Option[FiniteDuration]]("baker-split-brain-resolver.stable-after")
      .getOrElse(throw new IllegalArgumentException("Invalid config: Missing baker-split-brain-resolver.stable-after"))

    // This check is to prevent so frequent split brain checks
    if (stableAfter < 1.second) throw new IllegalArgumentException("Invalid config: baker-split-brain-resolver.stable-after should be greater than 1 second")
    else stableAfter
  }

  override def downingActorProps: Option[Props] = Some(SplitBrainResolverActor.props(downRemovalMargin))
}
