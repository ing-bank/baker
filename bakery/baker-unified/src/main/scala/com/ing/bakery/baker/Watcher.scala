package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.typesafe.config.Config

import scala.concurrent.ExecutionContext

object Watcher {

  def resource(config: Config, system: ActorSystem)(implicit cs: ContextShift[IO], timer: Timer[IO], ec: ExecutionContext): Resource[IO, Unit] = {

    val watcher = config.getString("baker.watcher")

    if (watcher != "") {
      Class.forName(watcher).getDeclaredConstructor().newInstance() match {
        case w: Watcher =>
          w.resource(config, system)
        case _ =>
          throw new IllegalArgumentException(s"Class $watcher defined in bakery.proxy-filter must extend com.ing.bakery.baker.Watcher")
      }
    } else Resource.liftF(IO.unit)
  }
}


trait Watcher {
  def resource(config: Config, system: ActorSystem): Resource[IO, Unit]
  def trigger: Unit
}
