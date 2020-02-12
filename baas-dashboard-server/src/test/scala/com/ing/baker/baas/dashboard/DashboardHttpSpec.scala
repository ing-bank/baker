package com.ing.baker.baas.dashboard

import java.util.UUID

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.data.StateT
import cats.effect.{ContextShift, IO, Timer}
import cats.implicits._
import com.ing.baker.baas.akka.{DashboardClient, DashboardHttp, RemoteBakerEventListenerClient}
import com.ing.baker.baas.dashboard.BakerEventEncoders._
import com.ing.baker.baas.dashboard.BakeryApi.{CacheRecipeInstanceMetadata, CacheRecipeMetadata}
import com.ing.baker.baas.dashboard.DashboardHttpSpec.test
import com.ing.baker.baas.test.{CheckoutFlowEvents, CheckoutFlowIngredients, CheckoutFlowRecipe}
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.runtime.serialization.Encryption
import io.circe.syntax._
import io.circe.generic.auto._
import org.scalatest.compatible.Assertion
import org.scalatest.{Matchers, fixture}

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future}
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
          _ <- IO.sleep(3.minutes).unsafeToFuture()
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
            recipeAddedR <- context.dashboardClient.getRecipe(recipe.recipeId)
            recipeInstanceCreated <- context.dashboardClient.getRecipeInstance(recipe.recipeId, recipeInstanceId)
            recipeMetadata <- context.dashboardClient.listRecipes
            recipeInstances <- context.dashboardClient.listInstances(recipe.recipeId)
            allEvents <- context.dashboardClient.listRecipeInstanceEvents(recipe.recipeId, recipeInstanceId)
          } yield {
            val expectedRecipeAdded = RecipeAdded(recipe.name, recipe.recipeId, 0, recipe)
            val expectedRecipeInstanceCreated = RecipeInstanceCreated(0, recipe.recipeId, recipe.name, recipeInstanceId)
            recipeAddedR shouldBe DashboardHttp.encodeResponseJson(expectedRecipeAdded)
            recipeInstanceCreated shouldBe DashboardHttp.encodeResponseJson(expectedRecipeAdded -> expectedRecipeInstanceCreated)
            recipeMetadata shouldBe DashboardHttp.encodeResponseJson(List(
              CacheRecipeMetadata(recipe.recipeId, recipe.name, 1, 0)))
            recipeInstances shouldBe DashboardHttp.encodeResponseJson(List(
              CacheRecipeInstanceMetadata(recipe.recipeId, recipeInstanceId, 0)))
            allEvents shouldBe DashboardHttp.encodeResponseJson(List(
              recipeAdded.asJson,
              instanceCreated.asJson,
              eventReceived.asJson,
              interactionStarted.asJson,
              interactionFailed.asJson
            ))
          }
        }
      } yield succeed
    }
  }
}

object DashboardHttpSpec {

  case class TestContext(
    dashboardClient: DashboardClient,
    fireBakerEvent: BakerEvent => Future[Unit]
  ) {

    def within[A](time: FiniteDuration)(f: => Future[A])(implicit timer: Timer[IO], cs: ContextShift[IO]): Future[A] = {
      def inner(count: Int, times: FiniteDuration, fio: IO[A]): IO[A] =
        if (count < 1) fio else fio.attempt.flatMap {
          case Left(_) => IO.sleep(times) *> inner(count - 1, times, fio)
          case Right(a) => IO(a)
        }
      val split = 5
      inner(split, time / split, IO.fromFuture(IO(f))).unsafeToFuture()
    }
  }

  def test[F[_], Lang <: LanguageApi]
  (runTest: TestContext => Future[Assertion])
  (implicit ec: ExecutionContext, timer: Timer[IO], cs: ContextShift[IO]): Future[Assertion] = {
    val testId: UUID = UUID.randomUUID()
    val systemName: String = "baas-node-interaction-test-" + testId
    implicit val system: ActorSystem = ActorSystem(systemName)
    implicit val materializer: Materializer = ActorMaterializer()
    implicit val encryption: Encryption = Encryption.NoEncryption
    for {
      (bakeryApi, bakerEventListenerPort) <- withOpenPort(5000,
        BakeryApi.runWith("http://localhost:MOCK_SERVER_PORT", _).unsafeToFuture())
      (dashboardApiBinding, dashboardApiPort) <- withOpenPort(5005,
        DashboardHttp.run(bakeryApi)( "0.0.0.0", _))

      bakerEventListenerClient = RemoteBakerEventListenerClient(s"http://localhost:$bakerEventListenerPort")
      dashboardApiClient = DashboardClient(s"http://localhost:$dashboardApiPort")

      context = TestContext(dashboardApiClient, bakerEventListenerClient.apply)

      assertionTry <- runTest(context).transform(Success(_))
      _ <- dashboardApiBinding.unbind()
      _ <- system.terminate()
      _ <- system.whenTerminated
      assertion <- Future.fromTry(assertionTry)
    } yield assertion
  }

  private def withOpenPort[T](from: Int, f: Int => Future[T])(implicit ec: ExecutionContext): Future[(T, Int)] = {
    def search(ports: Stream[Int]): Future[(Stream[Int], (T, Int))] =
      ports match {
        case #::(port1, tail) => f(port1).map(tail -> (_, port1)).recoverWith {
          case _: java.net.BindException => search(tail)
          case other => println("REVIEW withOpenPort function implementation, uncaught exception: " + Console.RED + other + Console.RESET); Future.failed(other)
        }
      }
    StateT(search).run(Stream.from(from, 1)).map(_._2)
  }
}
