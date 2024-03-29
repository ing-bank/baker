package com.ing.bakery.components

import akka.actor.ActorSystem
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.typesafe.config.ConfigFactory
import org.scalatest.concurrent.Eventually
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.must.Matchers

import java.util.UUID
import scala.concurrent.ExecutionContext

class WatcherSpec extends AnyFunSuite with Matchers with Eventually {

  test("Watcher starts") {
    val config = ConfigFactory.load("application-watcher.conf")
    implicit val executionContext: ExecutionContext = ExecutionContext.global
    implicit val timer: Timer[IO] = IO.timer(executionContext)
    implicit val contextShift: ContextShift[IO] = IO.contextShift(executionContext)
    val s = (for {
      system <- Resource.make(IO {
        ActorSystem(UUID.randomUUID().toString, ConfigFactory.parseString(
          """
            |akka {
            |  stdout-loglevel = "OFF"
            |  loglevel = "OFF"
            |}
            |""".stripMargin)) })((system: ActorSystem) => IO.fromFuture(IO {
        system.terminate().flatMap(_ => system.whenTerminated) })(contextShift).void)
      _ <- Watcher.resource(config, system, None)

    } yield ())

    assert(!WatcherReadinessCheck.ready)
    s.use(_ => IO.unit).unsafeRunAsyncAndForget()

    assert(TestWatcher.started)
    eventually {
      assert(WatcherReadinessCheck.ready)
    }
    assert(!TestWatcher.triggered)
    eventually {
      assert(TestWatcher.triggered)
    }

  }


}

