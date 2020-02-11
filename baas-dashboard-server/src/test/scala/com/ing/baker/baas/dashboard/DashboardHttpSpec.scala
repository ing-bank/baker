package com.ing.baker.baas.dashboard

import java.util.UUID

import cats.implicits._
import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.data.StateT
import com.ing.baker.baas.akka.RemoteBakerEventListenerClient
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.runtime.scaladsl.{BakerEvent, RecipeInstanceCreated}
import com.ing.baker.runtime.serialization.Encryption
import org.scalatest.AsyncFlatSpec
import org.scalatest.compatible.Assertion
import com.ing.baker.baas.dashboard.DashboardHttpSpec.test

import scala.concurrent.{ExecutionContext, Future, Promise}
import scala.concurrent.duration._
import scala.util.Success

class DashboardHttpSpec extends AsyncFlatSpec {

  val testEvent = RecipeInstanceCreated(1, "recipe-id", "recipe-name", "recipe-instance-id")

  "Dashboard Server" should "test" in {
    test { context =>
      for {
        _ <- context.fireBakerEvent(testEvent)
        _ <- context.wait(1.second)
        _ = println(Console.MAGENTA + "FIRST" + Console.RESET)
        _ = context.bakeryApi.logEvents.unsafeRunAsyncAndForget()
        _ = println(Console.MAGENTA + "SECOND" + Console.RESET)
        _ <- context.fireBakerEvent(testEvent)
        _ <- context.wait(3 seconds)
      } yield succeed
    }
  }
}

object DashboardHttpSpec {

  case class TestContext(
    bakeryApi: BakeryApi,
    fireBakerEvent: BakerEvent => Future[Unit],
    system: ActorSystem
  ) {

    def wait(time: FiniteDuration): Future[Unit] = {
      val promise: Promise[Unit] = Promise()
      system.scheduler.scheduleOnce(time)(promise.complete(Success(())))(system.dispatcher)
      promise.future
    }
  }

  def test[F[_], Lang <: LanguageApi]
  (runTest: TestContext => Future[Assertion])
  (implicit ec: ExecutionContext): Future[Assertion] = {
    val testId: UUID = UUID.randomUUID()
    val systemName: String = "baas-node-interaction-test-" + testId
    implicit val system: ActorSystem = ActorSystem(systemName)
    implicit val materializer: Materializer = ActorMaterializer()
    implicit val encryption: Encryption = Encryption.NoEncryption
    for {
      (bakeryApi, (_, bakerEventListenerPort)) <- withOpenPorts(5000, (port1, port2) =>
        BakeryApi.runWith("http://localhost:MOCK_SERVER_PORT", port2).unsafeToFuture())
      bakerEventListenerClient = RemoteBakerEventListenerClient(s"http://localhost:$bakerEventListenerPort")
      context = TestContext(bakeryApi, bakerEventListenerClient(_), system)
      assertion <- runTest(context)
      _ <- system.terminate()
      _ <- system.whenTerminated
    } yield assertion
  }

  private def withOpenPorts[T](from: Int, f: (Int, Int) => Future[T])(implicit ec: ExecutionContext): Future[(T, (Int, Int))] = {
    def search(ports: Stream[Int]): Future[(Stream[Int], (T, (Int, Int)))] =
      ports match {
        case #::(port1, #::(port2, tail)) => f(port1, port2).map(tail -> (_, (port1, port2))).recoverWith {
          case _: java.net.BindException => search(tail)
          case other => println("REVIEW withOpenPort function implementation, uncaught exception: " + Console.RED + other + Console.RESET); Future.failed(other)
        }
      }
    StateT(search).run(Stream.from(from, 1)).map(_._2)
  }
}