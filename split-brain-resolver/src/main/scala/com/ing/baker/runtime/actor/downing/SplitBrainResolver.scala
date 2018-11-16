package com.ing.baker.runtime.actor.downing

import akka.actor.{ActorSystem, Props}
import akka.cluster.DowningProvider
import net.ceedubs.ficus.Ficus._

import scala.concurrent.duration.FiniteDuration

class SplitBrainResolver(actorSystem: ActorSystem) extends DowningProvider {

  override val downRemovalMargin: FiniteDuration = actorSystem.settings.config.as[FiniteDuration]("baker.cluster.split-brain-resolver.down-removal-margin")

  override def downingActorProps: Option[Props] = Some(SplitBrainResolverActor.props(downRemovalMargin))
}
