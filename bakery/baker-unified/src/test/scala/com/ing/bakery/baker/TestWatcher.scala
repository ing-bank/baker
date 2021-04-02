package com.ing.bakery.baker
import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.typesafe.config.Config

object TestWatcher {
  var started = false
}

class TestWatcher extends Watcher {
  override def resource(config: Config, system: ActorSystem): Resource[IO, Unit] =
    Resource.liftF(IO(TestWatcher.started = true))
}
