package com.ing.baker.runtime.scaladsl

import akka.actor.ActorSystem
import com.ing.baker.runtime.common.ScalaBaker
import com.ing.baker.runtime.akka.AkkaBaker
import com.typesafe.config.{Config, ConfigFactory}

import scala.concurrent.Future

/**
  * The Baker is the component of the Baker library that runs one or multiples recipes.
  * For each recipe a new instance can be baked, sensory events can be send and state can be inquired upon
  */
trait Baker extends ScalaBaker[Future]

object Baker {

  def akka(config: Config, actorSystem: ActorSystem): AkkaBaker =
    new AkkaBaker(config)(actorSystem)

  def akka(actorSystem: ActorSystem): AkkaBaker =
    akka(ConfigFactory.load(), actorSystem)

}