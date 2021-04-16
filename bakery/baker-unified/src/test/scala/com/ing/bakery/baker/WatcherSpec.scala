package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.ing.baker.runtime.akka.internal.LocalInteractions
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.bakery.mocks.EventListener
import com.ing.bakery.testing.BakeryFunSpec
import com.typesafe.config.ConfigFactory
import org.http4s.Status.Ok
import org.http4s.client.blaze.BlazeClientBuilder
import org.scalatest.concurrent.Eventually
import org.scalatest.freespec.AnyFreeSpec
import org.scalatest.funspec.FixtureAsyncFunSpecLike
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.must.Matchers

import java.io.File
import java.net.InetSocketAddress
import java.util.UUID
import scala.concurrent.ExecutionContext
import cats.effect.Temporal

class WatcherSpec extends AnyFunSuite with Matchers with Eventually {

  test("Watcher starts") {
    val config = ConfigFactory.load("application-watcher.conf")
    implicit val executionContext: ExecutionContext = ExecutionContext.global
    implicit val timer: Temporal[IO] = IO.timer(executionContext)
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
      _ <- Watcher.resource(config, system)

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

