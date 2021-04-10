package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.typesafe.config.Config

import scala.concurrent.{ExecutionContext, Future}
import cats.effect.Temporal

object WatcherReadinessCheck {
  var ready: Boolean = false
  def enable(): Unit = { WatcherReadinessCheck.ready = true }
}

class WatcherReadinessCheck extends (() => Future[Boolean]) {
  override def apply(): Future[Boolean] = Future.successful(WatcherReadinessCheck.ready)
}

object Watcher {

  def resource(config: Config, system: ActorSystem)(implicit timer: Temporal[IO], ec: ExecutionContext): Resource[IO, Unit] = {

    val watcher = config.getString("baker.watcher.class")

    if (watcher != "") {
      Class.forName(watcher).getDeclaredConstructor().newInstance() match {
        case w: Watcher =>
          w.resource(config, system, WatcherReadinessCheck.enable())
        case _ =>
          throw new IllegalArgumentException(s"Class $watcher defined in bakery.proxy-filter must extend com.ing.bakery.baker.Watcher")
      }
    } else Resource.eval(IO(WatcherReadinessCheck.enable()))
  }
}


trait Watcher {
  def resource(config: Config, system: ActorSystem, callbackEnable: => Unit): Resource[IO, Unit]
  def trigger: Unit
}
