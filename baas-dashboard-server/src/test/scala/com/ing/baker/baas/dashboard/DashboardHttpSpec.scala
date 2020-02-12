package com.ing.baker.baas.dashboard

import java.util.UUID

import cats.implicits._
import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.data.StateT
import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.baas.akka.RemoteBakerEventListenerClient
import com.ing.baker.baas.dashboard.BakeryApi.{CacheRecipeInstanceMetadata, CacheRecipeMetadata}
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.runtime.scaladsl.{BakerEvent, EventInstance, EventReceived, InteractionFailed, InteractionStarted, RecipeAdded, RecipeInstanceCreated}
import com.ing.baker.runtime.serialization.Encryption
import org.scalatest.{AsyncFlatSpec, ConfigMap, Matchers, fixture}
import org.scalatest.compatible.Assertion
import com.ing.baker.baas.dashboard.DashboardHttpSpec.test
import com.ing.baker.baas.test.{CheckoutFlowEvents, CheckoutFlowIngredients, CheckoutFlowRecipe}
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import BakerEventEncoders._
import io.circe.syntax._

import scala.concurrent.{ExecutionContext, Future}
import scala.concurrent.duration._
import scala.util.Success

class DashboardHttpSpec extends fixture.AsyncFlatSpec with Matchers {

  implicit val cs: ContextShift[IO] = IO.contextShift(executionContext)

  implicit val timer: Timer[IO] = IO.timer(executionContext)

  val recipe = CheckoutFlowRecipe.compiledRecipe

  val event = CheckoutFlowEvents.OrderPlaced(
    CheckoutFlowIngredients.OrderId("order-id"), List(CheckoutFlowIngredients.Item("item-1")))

  val recipeInstanceId = "instance-id"

  val recipeAdded = RecipeAdded(recipe.name, recipe.recipeId, 0, recipe)

  val instanceCreated = RecipeInstanceCreated(0, recipe.recipeId, recipe.name, recipeInstanceId)

  val eventReceived = EventReceived(0, recipe.name, recipe.recipeId, recipeInstanceId, None, EventInstance.unsafeFrom(event))

  val interactionStarted = InteractionStarted(0, recipe.name, recipe.recipeId, recipeInstanceId, "FirstInteraction")

  val interactionFailed = InteractionFailed(0, 5, recipe.name, recipe.recipeId, recipeInstanceId, "FirstInteraction",
    1, new RuntimeException("Some error description"), ExceptionStrategyOutcome.BlockTransition)

  override type FixtureParam = Boolean

  override def withFixture(test: OneArgAsyncTest) = {
    val mock = test.configMap.getOptional[Boolean]("mock").getOrElse(false)
    withFixture(test.toNoArgAsyncTest(mock))
  }

  "Dashboard Server" should "run the test server" in { mock =>
    if (mock)
      test { context =>
        for {
          _ <- context.fireBakerEvent(recipeAdded)
          _ <- context.fireBakerEvent(instanceCreated)
          _ <- context.fireBakerEvent(eventReceived)
          _ <- context.fireBakerEvent(interactionStarted)
          _ <- context.fireBakerEvent(interactionFailed)
          _ <- IO.never
        } yield succeed
      }
    else Future.successful(succeed)
  }

  it should "process baker events" in { _ =>
    test { context =>
      for {
        _ <- context.fireBakerEvent(recipeAdded)
        _ <- context.fireBakerEvent(instanceCreated)
        _ <- context.fireBakerEvent(eventReceived)
        _ <- context.fireBakerEvent(interactionStarted)
        _ <- context.fireBakerEvent(interactionFailed)
        _ <- context.within(2.seconds) {
          for {
            recipeMetadata <- context.bakeryApi.listRecipes
            recipeInstances <- context.bakeryApi.listInstances(recipe.recipeId)
            allEvents <- context.bakeryApi.listEvents(recipe.recipeId, recipeInstanceId)
          } yield {
            recipeMetadata shouldBe List(CacheRecipeMetadata(recipe.recipeId, recipe.name, 1, 0))
            recipeInstances shouldBe List(CacheRecipeInstanceMetadata(recipe.recipeId, recipeInstanceId, 0))
            allEvents shouldBe List(
              recipeAdded.asJson,
              instanceCreated.asJson,
              eventReceived.asJson,
              interactionStarted.asJson,
              interactionFailed.asJson
            )
          }
        }
      } yield succeed
    }
  }
}

object DashboardHttpSpec {

  case class TestContext(
    bakeryApi: BakeryApi,
    fireBakerEvent: BakerEvent => IO[Unit]
  ) {

    def within[A](time: FiniteDuration)(f: IO[A])(implicit timer: Timer[IO]): IO[A] = {
      def inner(count: Int, times: FiniteDuration): IO[A] =
        if (count < 1) f else f.attempt.flatMap {
          case Left(_) => IO.sleep(times) *> inner(count - 1, times)
          case Right(a) => IO(a)
        }
      val split = 5
      inner(split, time / split)
    }
  }

  def test[F[_], Lang <: LanguageApi]
  (runTest: TestContext => IO[Assertion])
  (implicit ec: ExecutionContext, timer: Timer[IO], cs: ContextShift[IO]): Future[Assertion] = {
    val testId: UUID = UUID.randomUUID()
    val systemName: String = "baas-node-interaction-test-" + testId
    implicit val system: ActorSystem = ActorSystem(systemName)
    implicit val materializer: Materializer = ActorMaterializer()
    implicit val encryption: Encryption = Encryption.NoEncryption
    for {
      (bakeryApi, (_, bakerEventListenerPort)) <- withOpenPorts(5000, (port1, port2) =>
        BakeryApi.runWith("http://localhost:MOCK_SERVER_PORT", port2).unsafeToFuture())
      bakerEventListenerClient = RemoteBakerEventListenerClient(s"http://localhost:$bakerEventListenerPort")
      context = TestContext(bakeryApi, event => IO.fromFuture(IO(bakerEventListenerClient(event))))
      assertionTry <- runTest(context).unsafeToFuture().transform(Success(_))
      _ <- system.terminate()
      _ <- system.whenTerminated
      assertion <- Future.fromTry(assertionTry)
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