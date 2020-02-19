package com.ing.baker.baas.dashboard

import java.net.InetSocketAddress
import java.util.UUID

import akka.actor.ActorSystem
import akka.stream.ActorMaterializer
import cats.effect.{IO, Resource}
import cats.implicits._
import com.ing.baker.baas.akka.RemoteBakerEventListenerClient
import com.ing.baker.baas.dashboard.BakerEventEncoders._
import com.ing.baker.baas.dashboard.BakeryStateCache.{CacheRecipeInstanceMetadata, CacheRecipeMetadata}
import com.ing.baker.baas.dashboard.DashboardSpec._
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.runtime.serialization.Encryption
import io.circe.generic.auto._
import io.circe.syntax._
import org.http4s.Uri
import org.http4s.client.blaze.BlazeClientBuilder
import org.scalatest.{ConfigMap, Matchers}

import scala.concurrent.duration._

object DashboardSpec {

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

}

class DashboardSpec extends BakeryFunSpec with Matchers {

  case class Args(runMockService: Boolean)

  case class Context(dashboardClient: DashboardClient, fireBakerEvent: BakerEvent => IO[Unit], runMockService: Boolean)

  /** Represents the "sealed resources context" that each test can use. */
  override type TestContext = Context

  /** Represents external arguments to the test context builder. */
  override type TestArguments = Args

  /** Creates a `Resource` which allocates and liberates the expensive resources each test can use.
    * For example web servers, network connection, database mocks.
    *
    * The objective of this function is to provide "sealed resources context" to each test, that means context
    * that other tests simply cannot touch.
    *
    * @param testArguments arguments built by the `argumentsBuilder` function.
    * @return the resources each test can use
    */
  override def contextBuilder(testArguments: TestArguments): Resource[IO, TestContext] = {
    for {
      system <- Resource.make(IO {
        val testId: UUID = UUID.randomUUID()
        val systemName: String = "baas-node-interaction-test-" + testId
        ActorSystem(systemName)
      })(system => IO.fromFuture(IO(system.terminate().flatMap(_ => system.whenTerminated))).void)
      config = DashboardDependencies(
        stateNodeAddress = InetSocketAddress.createUnresolved("0.0.0.0", 8080),
        eventListenerAddress = InetSocketAddress.createUnresolved("0.0.0.0", 0),
        dashboardServiceAddress = InetSocketAddress.createUnresolved("0.0.0.0", 0),
        _system = system,
        _materializer = ActorMaterializer()(system),
        _encryption = Encryption.NoEncryption
      )
      dashboardServiceComponents <- DashboardService.resource(config)
      http4sClient = BlazeClientBuilder[IO](executionContext).resource
      bakerEventListenerClient = RemoteBakerEventListenerClient(s"http://localhost:${dashboardServiceComponents.eventListenerAddress.getPort}")(system, config.materializer, config.encryption)
      dashboardClient = new DashboardClient(http4sClient, Uri.unsafeFromString(s"http://localhost:${dashboardServiceComponents.serverAddress.getPort}"))
    } yield Context(
      dashboardClient = dashboardClient,
      fireBakerEvent = event => IO.fromFuture(IO(bakerEventListenerClient.apply(event))),
      runMockService = testArguments.runMockService
    )
  }

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
    *
    * @param config map populated with the -Dkey=value arguments.
    * @return the data structure used by the `contextBuilder` function.
    */
  override def argumentsBuilder(config: ConfigMap): TestArguments =
    Args(runMockService = config.getOptional[Boolean]("mock").getOrElse(false))


  describe("Dashboard Service") {

    test("run the test server") { context =>
      if (context.runMockService)
        for {
          _ <- context.fireBakerEvent(recipeAdded)
          _ <- context.fireBakerEvent(instanceCreated)
          _ <- context.fireBakerEvent(eventReceived)
          _ <- context.fireBakerEvent(interactionStarted)
          _ <- context.fireBakerEvent(interactionFailed)
          _ <- IO.sleep(3.minutes)
        } yield succeed
      else IO.pure(succeed)
    }

    test("process baker events") { context =>
      for {
        _ <- context.fireBakerEvent(recipeAdded)
        _ <- context.fireBakerEvent(instanceCreated)
        _ <- context.fireBakerEvent(eventReceived)
        _ <- context.fireBakerEvent(interactionStarted)
        _ <- context.fireBakerEvent(interactionFailed)
        _ <- eventually {
          for {
            recipeAddedR <- context.dashboardClient.getRecipe(recipe.recipeId)
            recipeInstanceCreated <- context.dashboardClient.getRecipeInstance(recipe.recipeId, recipeInstanceId)
            recipeMetadata <- context.dashboardClient.listRecipes
            recipeInstances <- context.dashboardClient.listInstances(recipe.recipeId)
            allEvents <- context.dashboardClient.listRecipeInstanceEvents(recipe.recipeId, recipeInstanceId)
          } yield {
            val expectedRecipeAdded = RecipeAdded(recipe.name, recipe.recipeId, 0, recipe)
            val expectedRecipeInstanceCreated = RecipeInstanceCreated(0, recipe.recipeId, recipe.name, recipeInstanceId)
            recipeAddedR shouldBe DashboardService.commonEncode(expectedRecipeAdded)
            recipeInstanceCreated shouldBe DashboardService.commonEncode(expectedRecipeAdded -> expectedRecipeInstanceCreated)
            recipeMetadata shouldBe DashboardService.commonEncode(List(
              CacheRecipeMetadata(recipe.recipeId, recipe.name, 1, 0)))
            recipeInstances shouldBe DashboardService.commonEncode(List(
              CacheRecipeInstanceMetadata(recipe.recipeId, recipeInstanceId, 0)))
            allEvents shouldBe DashboardService.commonEncode(List(
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
