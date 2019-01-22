package com.ing.baker.baas

import java.util.UUID

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.baas.BAASSpec.{InteractionOne, _}
import com.ing.baker.baas.server.BAASAPI
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.scaladsl
import com.ing.baker.recipe.scaladsl._
import com.ing.baker.runtime.core.{AkkaBaker, Baker, BakerProvider, ProcessState, RuntimeEvent, SensoryEventStatus}
import org.scalatest.{BeforeAndAfterAll, Matchers, WordSpecLike}

import scala.concurrent.Await
import scala.concurrent.duration._

class BAASSpec extends TestKit(ActorSystem("BAASSpec")) with WordSpecLike with Matchers with BeforeAndAfterAll {
  def actorSystemName: String = "BAASSpec"

  val baasHost = "localhost"
  val baasPort = 8081

  // Startup a empty BAAS cluster
  val baker = new AkkaBaker()(system)
  val baasAPI: BAASAPI = new BAASAPI(baker, baasHost, baasPort)(system)

  // Start a BAAS API
  val baasClient: Baker = BakerProvider()

  // implementations
  val localImplementations: Seq[AnyRef] = Seq(InteractionOne(), InteractionTwo())


  override def beforeAll() {
    Await.result(baasAPI.start(), 10 seconds)
    baasClient.addImplementations(localImplementations)
  }

  override def afterAll() {
    Await.result(baasAPI.stop(), 10 seconds)
  }

  "Happy flow simple recipe BAAS" in {

    val recipeName = "simpleRecipe" + UUID.randomUUID().toString
    val recipe: Recipe = setupSimpleRecipe(recipeName)
    val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
    val recipeId = baasClient.addRecipe(compiledRecipe)

    val requestId = UUID.randomUUID().toString

    baasClient.bake(recipeId, requestId)

    val sensoryEventStatusResponse: SensoryEventStatus =
      baasClient.processEvent(requestId, InitialEvent("initialIngredient"))
    sensoryEventStatusResponse shouldBe SensoryEventStatus.Completed

    val processState: ProcessState = baasClient.getProcessState(requestId)

    processState.ingredients.keys should contain("initialIngredient")
    processState.ingredients.keys should contain("interactionOneIngredient")

    val events: Seq[RuntimeEvent] = baasClient.events(requestId)

    println(s"events: $events")
    println(s"procesState : ${processState.ingredients}")
  }
}

object BAASSpec {

  val initialIngredient = Ingredient[String]("initialIngredient")
  val interactionOneIngredient = Ingredient[String]("interactionOneIngredient")

  val initialEvent = Event("InitialEvent", initialIngredient)
  case class InitialEvent(initialIngredient: String)
  case class InteractionOneEvent(interactionOneIngredient: String)

  val interactionOne =
    Interaction(
      name = "InteractionOne",
      inputIngredients = Seq(processId, initialIngredient),
      output = Seq(Event[InteractionOneEvent]))

  case class InteractionOne() {
    def name: String = "InteractionOne"
    def apply(processId: String, initialIngredient: String): InteractionOneEvent = {
      println("Executing interactionOne")
      InteractionOneEvent(initialIngredient)
    }
  }

  case class InteractionTwo() {
    def name: String = "InteractionTwo"
    def apply(processId: String, initialIngredient: String): String = {
      println("Executing InteractionTwo")
      initialIngredient
    }
  }

  def setupSimpleRecipe(name: String): scaladsl.Recipe = {
    scaladsl.Recipe(name)
      .withInteraction(interactionOne)
      .withSensoryEvent(initialEvent)
  }

}
