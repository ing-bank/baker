package com.ing.baker.baas

import java.util.UUID

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.baas.BAASSpec.{InteractionOne, _}
import com.ing.baker.baas.http.BAASAPI
import com.ing.baker.recipe.common.ProvidesIngredient
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Ingredients, Interaction, processId}
import com.ing.baker.recipe.{commonserialize, scaladsl}
import com.ing.baker.runtime.core.{ProcessState, SensoryEventStatus}
import org.scalatest.{BeforeAndAfterAll, Matchers, WordSpecLike}

import scala.concurrent.Await
import scala.concurrent.duration._

class BAASSpec extends TestKit(ActorSystem("BAASAPIActorSystem")) with WordSpecLike with Matchers with BeforeAndAfterAll {
  def actorSystemName: String = "BAASSpec"

  val host = "localhost"
  val port = 8081

//  Startup a empty BAAS cluster
  val baasAPI: BAASAPI = new BAASAPI(new BAAS(), host, port)(system)
  Await.result(baasAPI.start(), 10 seconds)

  //Start a BAAS API
  val baasClient: BAASClient = new BAASClient(host, port)

  baasClient.addImplementation(InteractionOne())


  "Serialize and deserialize a common recipe" in {
    val originalRecipe: commonserialize.Recipe = new commonserialize.Recipe(setupSimpleRecipe("name"))
    val serializedRecipe = BAAS.serializeRecipe(originalRecipe)
    val deserializedRecipe = BAAS.deserializeRecipe(serializedRecipe)

    deserializedRecipe shouldBe originalRecipe
  }

  "Send recipe to the BAAS API" in {
    val originalRecipe: scaladsl.Recipe = setupSimpleRecipe("recipename")
    baasClient.addRecipe(originalRecipe)
  }

  "Add a implementation to the BAAS API" in {
    baasClient.addImplementation(InteractionTwo());
  }

  "Happy flow simple recipe BAAS" in {
    val recipeName = "simpleRecipe" + UUID.randomUUID().toString
    val recipe = setupSimpleRecipe(recipeName)

    baasClient.addRecipe(recipe)

    val requestId = UUID.randomUUID().toString

    baasClient.bake(recipeName, requestId)

    val sensoryEventStatusResponse: SensoryEventStatus = baasClient.handleEvent(recipeName, requestId, InitialEvent("initialIngredient"))
    sensoryEventStatusResponse shouldBe SensoryEventStatus.Completed

    val processState: ProcessState = baasClient.getState(recipeName, requestId)

    processState.ingredients.keys should contain("initialIngredient")
    processState.ingredients.keys should contain("interactionOneIngredient")
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

  val interactionOne =
    Interaction("InteractionOne",
      Ingredients(processId, initialIngredient),
      ProvidesIngredient(interactionOneIngredient))

  case class InteractionOne() {
    def name: String = "InteractionOne"
    def apply(processId: String, initialIngredient: String): String = {
      println("Executing interactionOne")
      initialIngredient
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
