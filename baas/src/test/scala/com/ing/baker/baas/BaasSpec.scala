package com.ing.baker.baas

import java.util.UUID

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.baas.BaasSpec.{InteractionOne, InteractionTwo, _}
import com.ing.baker.baas.server.BaasServer
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.javadsl.InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder
import com.ing.baker.recipe.scaladsl
import com.ing.baker.recipe.scaladsl._
import com.ing.baker.runtime.core.{AkkaBaker, Baker, BakerProvider, BakerResponse, ProcessState, RuntimeEvent, SensoryEventStatus}
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
  val baker = new AkkaBaker()(system)
  val baasAPI: BaasServer = new BaasServer(baker, baasHost, baasPort)(system)

  // Start a BAAS API
  val baasBaker: Baker = BakerProvider()

  val mockOne = mock(classOf[InteractionOne])
  val mockTwo = mock(classOf[InteractionTwo])


  // implementations
  val localImplementations: Seq[AnyRef] = Seq(mockOne, mockTwo)


  override def beforeAll() {
    reset(mockOne, mockTwo)
    Await.result(baasAPI.start(), 10 seconds)
    baasBaker.addImplementations(localImplementations)
  }

  override def afterAll() {
    Await.result(baasAPI.stop(), 10 seconds)
  }

  "Happy flow simple recipe BAAS" in {
    when(mockOne.apply(anyString(), anyString()))
      .thenReturn(InteractionOneEvent("InteractionOneOutput"))

    when(mockTwo.apply(anyString(), anyString()))
      .thenThrow(new RuntimeException("InteractionTwoFailure"))
      .thenReturn(InteractionTwoEvent("InteractionTwoOutput"))

    val recipeName = "simpleRecipe" + UUID.randomUUID().toString
    val recipe: Recipe = setupSimpleRecipe(recipeName)
    val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
    val recipeId = baasBaker.addRecipe(compiledRecipe)

    val requestId = UUID.randomUUID().toString

    baasBaker.bake(recipeId, requestId)

    val sensoryEventStatusResponse: SensoryEventStatus =
      baasBaker.processEvent(requestId, InitialEvent("initialIngredient"))
    sensoryEventStatusResponse shouldBe SensoryEventStatus.Completed

    val processState: ProcessState = baasBaker.getProcessState(requestId)

    processState.ingredients.keys should contain("initialIngredient")
    processState.ingredients.keys should contain("interactionOneIngredient")
    processState.ingredients.keys should contain("interactionTwoIngredient")

    val events: Seq[RuntimeEvent] = baasBaker.events(requestId)

//    println(s"${Console.YELLOW} events: $events ${Console.RESET}")
//    println(s"procesState : ${processState.ingredients}")

    val visualState = baasBaker.getVisualState(requestId)

//    println(visualState)

  }

  "Process Event Async with http streaming" in {
    when(mockOne.apply(anyString(), anyString()))
      .thenReturn(InteractionOneEvent("InteractionOneOutput"))

    when(mockTwo.apply(anyString(), anyString()))
      .thenThrow(new RuntimeException("InteractionTwoFailure"))
      .thenReturn(InteractionTwoEvent("InteractionTwoOutput"))

    val recipeName = "simpleRecipe" + UUID.randomUUID().toString
    val recipe: Recipe = setupSimpleRecipe(recipeName)
    val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
    val recipeId = baasBaker.addRecipe(compiledRecipe)

    val requestId = UUID.randomUUID().toString


    baasBaker.bake(recipeId, requestId)

    val response: BakerResponse = baasBaker.processEventAsync(requestId, InitialEvent("initialIngredient"))

    val events: Seq[RuntimeEvent] = response.confirmAllEvents(60.second)
//    println(Console.YELLOW + events + Console.RESET)

    assert(events.nonEmpty)
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
