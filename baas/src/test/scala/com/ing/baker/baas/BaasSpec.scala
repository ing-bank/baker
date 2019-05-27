package com.ing.baker.baas

import java.util.UUID

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import akka.testkit.TestKit
import com.ing.baker.baas.BaasSpec._
import com.ing.baker.baas.client.BaasBaker
import com.ing.baker.baas.server.BaasServer
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.javadsl.InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder
import com.ing.baker.recipe.scaladsl
import com.ing.baker.recipe.scaladsl._
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.{Baker, RuntimeEvent}
import com.typesafe.config.{Config, ConfigFactory}
import org.mockito.Matchers.anyString
import org.mockito.Mockito.{mock, reset, when}
import org.scalatest.{BeforeAndAfterAll, Matchers, WordSpecLike}

import scala.concurrent.Await
import scala.concurrent.duration._

class BaasSpec extends TestKit(ActorSystem("BAASSpec")) with WordSpecLike with Matchers with BeforeAndAfterAll {
  def actorSystemName: String = "BAASSpec"

  val baasHost = "localhost"
  val baasPort = 8081

  // Startup a empty BAAS cluster
  val config: Config = ConfigFactory.load()
  val materializer: Materializer = ActorMaterializer.create(system)
  val baker = Baker.akka(config, system, materializer)
  val baasAPI: BaasServer = new BaasServer(baker, baasHost, baasPort)(system)

  // Start a BAAS API
  val baasBaker: Baker = new BaasBaker(
    config,
    config.getString("baker.engine.baas.client-host"),
    config.getInt("baker.engine.baas.client-port"),
    config.getString("baker.engine.baas.baas-host"),
    config.getInt("baker.engine.baas.baas-port"))

  import system.dispatcher

  override def afterAll() {
    Await.result(baasAPI.stop(), 10 seconds)
  }

  "Happy flow simple recipe BAAS" in {
    val mockOne = mock(classOf[InteractionOne])
    val mockTwo = mock(classOf[InteractionTwo])
    val localImplementations: Seq[AnyRef] = Seq(mockOne, mockTwo)
    Await.result(baasAPI.start(), 10 seconds)
    baasBaker.addImplementations(localImplementations)

    when(mockOne.apply(anyString(), anyString()))
      .thenReturn(InteractionOneEvent("InteractionOneOutput"))

    when(mockTwo.apply(anyString(), anyString()))
      .thenThrow(new RuntimeException("InteractionTwoFailure"))
      .thenReturn(InteractionTwoEvent("InteractionTwoOutput"))

    val recipeName = "simpleRecipe" + UUID.randomUUID().toString
    val recipe: Recipe = setupSimpleRecipe(recipeName)
    val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
    val requestId = UUID.randomUUID().toString

    for {
      recipeId <- baasBaker.addRecipe(compiledRecipe)
      _ <- baasBaker.bake(recipeId, requestId)
      response <- baasBaker.fireSensoryEventCompleted(requestId, RuntimeEvent.unsafeFrom(InitialEvent("initialIngredient")))
      _ = response.status shouldBe SensoryEventStatus.Completed
      processState <- baasBaker.getProcessState(requestId)

      _ = processState.ingredients.keys should contain("initialIngredient")
      _ = processState.ingredients.keys should contain("interactionOneIngredient")
      _ = processState.ingredients.keys should contain("interactionTwoIngredient")

      _ = baasBaker.getVisualState(requestId)
      //    println(visualState)
    } yield succeed
  }

  "Process Event Async with http streaming" in {
    val mockOne = mock(classOf[InteractionOne])
    val mockTwo = mock(classOf[InteractionTwo])
    val localImplementations: Seq[AnyRef] = Seq(mockOne, mockTwo)
    Await.result(baasAPI.start(), 10 seconds)
    baasBaker.addImplementations(localImplementations)

    when(mockOne.apply(anyString(), anyString()))
      .thenReturn(InteractionOneEvent("InteractionOneOutput"))

    when(mockTwo.apply(anyString(), anyString()))
      .thenReturn(InteractionTwoEvent("InteractionTwoOutput"))

    val recipeName = "simpleRecipe" + UUID.randomUUID().toString
    val recipe: Recipe = setupSimpleRecipe(recipeName)
    val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
    val requestId = UUID.randomUUID().toString

    for {
      recipeId <- baasBaker.addRecipe(compiledRecipe)
      _ <- baasBaker.bake(recipeId, requestId)
      response <- baasBaker.fireSensoryEventCompleted(requestId, RuntimeEvent.unsafeFrom(InitialEvent("initialIngredient")))
    } yield assert(response.events.nonEmpty)
  }
}

object BaasSpec {

  val initialIngredient = Ingredient[String]("initialIngredient")
  val interactionOneIngredient = Ingredient[String]("interactionOneIngredient")

  val initialEvent = Event("InitialEvent", initialIngredient)

  case class InitialEvent(initialIngredient: String)
  case class InteractionOneEvent(interactionOneIngredient: String)
  case class InteractionTwoEvent(interactionTwoIngredient: String)

  val interactionOne =
    Interaction(
      name = "InteractionOne",
      inputIngredients = Seq(processId, initialIngredient),
      output = Seq(Event[InteractionOneEvent]))

  trait InteractionOne {
    def name: String = "InteractionOne"
    def apply(processId: String, initialIngredient: String): InteractionOneEvent
  }

  val interactionTwo =
    Interaction(
      name = "InteractionTwo",
      inputIngredients = Seq(processId, initialIngredient),
      output = Seq(Event[InteractionTwoEvent]))

  trait InteractionTwo {
    def name: String = "InteractionTwo"
    def apply(processId: String, initialIngredient: String): InteractionTwoEvent
  }

  def setupSimpleRecipe(name: String): scaladsl.Recipe = {
    scaladsl.Recipe(name)
      .withInteractions(
        interactionOne,
        interactionTwo
      )
      .withSensoryEvent(
        initialEvent
      )
      .withDefaultFailureStrategy(
        new RetryWithIncrementalBackoffBuilder()
          .withInitialDelay(java.time.Duration.ofMillis(10l))
          .withMaximumRetries(10)
          .build()
      )
  }

}
