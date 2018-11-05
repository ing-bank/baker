package com.ing.baker.baas

import java.util.UUID

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.baas.BAASSpec.{InteractionOne, _}
import com.ing.baker.baas.http.BAASAPI
import com.ing.baker.baas.interaction.http.RemoteInteractionLauncher
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, processId}
import com.ing.baker.recipe.{commonserialize, scaladsl}
import com.ing.baker.runtime.core.internal.MethodInteractionImplementation
import com.ing.baker.runtime.core.{Baker, ProcessState, SensoryEventStatus}
import org.scalatest.{BeforeAndAfterAll, Matchers, WordSpecLike}

import scala.concurrent.Await
import scala.concurrent.duration._

class BAASSpec extends TestKit(ActorSystem("BAASSpec")) with WordSpecLike with Matchers with BeforeAndAfterAll {
  def actorSystemName: String = "BAASSpec"

  val host = "localhost"
  val port = 8081

//  Startup a empty BAAS cluster
  val baker = new Baker()(system)
  val baasAPI: BAASAPI = new BAASAPI(baker, host, port)(system)
  Await.result(baasAPI.start(), 10 seconds)

  //Start a BAAS API
  val baasClient: BAASClient = new BAASClient(host, port)

  // implementations
  val localImplementations = Seq(InteractionOne(), InteractionTwo())

  // host the local implementations
  val launcher = RemoteInteractionLauncher.apply(
    MethodInteractionImplementation.toImplementationMap(localImplementations), "localhost", 8090)

  launcher.start()


  "Happy flow simple recipe BAAS" ignore {
    val recipeName = "simpleRecipe" + UUID.randomUUID().toString
    val recipe = setupSimpleRecipe(recipeName)

    val recipeId = baasClient.addRecipe(recipe)

    val requestId = UUID.randomUUID().toString

    baasClient.bake(recipeId, requestId)

    val sensoryEventStatusResponse: SensoryEventStatus =
      baasClient.processEvent(requestId, InitialEvent("initialIngredient"), EventConfirmation.COMPLETED)
    sensoryEventStatusResponse shouldBe SensoryEventStatus.Completed

    val processState: ProcessState = baasClient.getState(requestId)

    processState.ingredients.keys should contain("initialIngredient")
    processState.ingredients.keys should contain("interactionOneIngredient")

    val events = baasClient.getEvents(requestId)

    println(s"events: $events")

//    println(s"procesState : ${requestState.processState}")
//    println(s"visualState : ${requestState.visualState}")
  }

  override def afterAll() = shutdown(system)
}

object BAASSpec {

  val initialIngredient = Ingredient[String]("initialIngredient")
  val interactionOneIngredient = Ingredient[String]("interactionOneIngredient")

  val initialEvent = Event("InitialEvent", initialIngredient, None)
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
