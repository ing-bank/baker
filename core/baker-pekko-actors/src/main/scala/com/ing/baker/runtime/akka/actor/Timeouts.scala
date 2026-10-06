package com.ing.baker.runtime.akka.actor

import com.typesafe.config.Config

import scala.concurrent.duration.FiniteDuration
import net.ceedubs.ficus.Ficus._

import scala.concurrent.duration._

case class Timeouts(defaultBakeTimeout: FiniteDuration,
                    defaultProcessEventTimeout: FiniteDuration,
                    defaultInquireTimeout: FiniteDuration,
                    defaultShutdownTimeout: FiniteDuration,
                    defaultAddRecipeTimeout: FiniteDuration,
                    defaultExecuteSingleInteractionTimeout: FiniteDuration)

object Timeouts {

  def default: Timeouts =
    Timeouts(
      defaultBakeTimeout = 10.seconds,
      defaultProcessEventTimeout = 10.seconds,
      defaultInquireTimeout = 10.seconds,
      defaultShutdownTimeout = 30.seconds,
      defaultAddRecipeTimeout = 10.seconds,
      defaultExecuteSingleInteractionTimeout = 60.seconds,
    )

  def apply(config: Config): Timeouts =
    Timeouts(
      defaultBakeTimeout = config.as[FiniteDuration]("baker.bake-timeout"),
      defaultProcessEventTimeout = config.as[FiniteDuration]("baker.process-event-timeout"),
      defaultInquireTimeout = config.as[FiniteDuration]("baker.process-inquire-timeout"),
      defaultShutdownTimeout = config.as[FiniteDuration]("baker.shutdown-timeout"),
      defaultAddRecipeTimeout = config.as[FiniteDuration]("baker.add-recipe-timeout"),
      defaultExecuteSingleInteractionTimeout = config.as[FiniteDuration]("baker.execute-single-interaction-timeout"),
    )
}

