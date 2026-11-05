package com.ing.bakery.components

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.typesafe.config.Config

import scala.concurrent.duration._
object TestWatcher {
  var started = false
  var triggered = false
}

class TestWatcher extends Watcher {

  override def trigger(): Unit = {
    TestWatcher.triggered = true
  }

  override def resource(config: Config, system: ActorSystem, cassandra: Option[Cassandra], callbackEnable: () => Unit): Resource[IO, Unit] = {
    Resource.eval(IO{
      TestWatcher.started = true
      callbackEnable()
    })
  }
}
