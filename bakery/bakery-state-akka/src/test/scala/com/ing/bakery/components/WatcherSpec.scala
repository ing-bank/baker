package com.ing.bakery.components

import akka.actor.ActorSystem
import cats.effect.unsafe.implicits.global
import cats.effect.{IO, Resource}
import com.typesafe.config.ConfigFactory
import org.scalatest.concurrent.Eventually
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.must.Matchers
import org.scalatest.time.SpanSugar.convertIntToGrainOfTime

import java.util.UUID
import scala.concurrent.ExecutionContext

class WatcherSpec extends AnyFunSuite with Matchers with Eventually {

  test("Watcher starts") {
    val config = ConfigFactory.load("application-watcher.conf")
    implicit val executionContext: ExecutionContext = ExecutionContext.global
    val s = for {
      system <- Resource.make(IO {
        ActorSystem(UUID.randomUUID().toString, ConfigFactory.parseString(
          """
            |akka {
            |  stdout-loglevel = "OFF"
            |  loglevel = "OFF"
            |}
            |""".stripMargin)) })((system: ActorSystem) => IO.fromFuture(IO {
        system.terminate().flatMap(_ => system.whenTerminated) }).void)
      _ <- Watcher.resource(config, system, None)
    } yield ()
    assert(!TestWatcher.started)
    assert(!WatcherReadinessCheck.ready)
    s.use(_ => {
      assert(TestWatcher.started)
      eventually {
        assert(WatcherReadinessCheck.ready)
      }
      assert(!TestWatcher.triggered)
      IO.unit
    }).unsafeRunSync()
  }
}

