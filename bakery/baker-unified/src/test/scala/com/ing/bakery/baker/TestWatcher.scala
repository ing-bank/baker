package com.ing.bakery.baker
import akka.actor.ActorSystem
import cats.effect.{IO, Resource, Timer}
import com.typesafe.config.Config
import cats.implicits._

import scala.concurrent.duration._
object TestWatcher {
  var started = false
  var triggered = false
}

class TestWatcher extends Watcher {

  override def trigger: Unit = TestWatcher.triggered = true

  override def resource(config: Config, system: ActorSystem): Resource[IO, Unit] = {
    implicit val timer: Timer[IO] = IO.timer(system.dispatcher)
    Resource.liftF(IO(TestWatcher.started = true) >> IO.sleep(100 millis) >> IO(TestWatcher.triggered = true) )
  }
}
