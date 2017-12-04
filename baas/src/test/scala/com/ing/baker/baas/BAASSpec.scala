package com.ing.baker.baas

import java.util.UUID

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.baas.BAASSpec.{InteractionOne, _}
import com.ing.baker.baas.http.BAASAPI
import com.ing.baker.baas.interaction.http.RemoteInteractionLauncher
import com.ing.baker.recipe.common.ProvidesIngredient
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Ingredients, Interaction, processId}
import com.ing.baker.recipe.{commonserialize, scaladsl}
import com.ing.baker.runtime.core.interations.MethodInteractionImplementation
import com.ing.baker.runtime.core.{ProcessState, SensoryEventStatus}
import org.scalatest.{BeforeAndAfterAll, Matchers, WordSpecLike}

import scala.concurrent.Await
import scala.concurrent.duration._

class BAASSpec extends TestKit(ActorSystem("BAASSpec")) with WordSpecLike with Matchers with BeforeAndAfterAll {
  def actorSystemName: String = "BAASSpec"

  val host = "localhost"
  val port = 8081

//  Startup a empty BAAS cluster
  val baasAPI: BAASAPI = new BAASAPI(new BAAS(system), host, port)(system)
  Await.result(baasAPI.start(), 10 seconds)

  //Start a BAAS API
  val baasClient: BAASClient = new BAASClient(host, port)

  // implementations
  val localImplementations = Seq(InteractionOne(), InteractionTwo())

  // host the local implementations
  val launcher = RemoteInteractionLauncher.apply(
    MethodInteractionImplementation.toImplementationMap(localImplementations), "localhost", 8090)

  launcher.start()


  "Serialize and deserialize a common recipe" in {
    val originalRecipe: commonserialize.Recipe = new commonserialize.Recipe(setupSimpleRecipe("name"))
    val serializedRecipe = BAAS.serializeRecipe(originalRecipe)
    val deserializedRecipe = BAAS.deserializeRecipe(serializedRecipe)

    deserializedRecipe shouldBe originalRecipe
  }

  "Add a implementation to the BAAS API" in {
    launcher.registerToBaker(baasClient)
  }

  "Send recipe to the BAAS API" in {
    val originalRecipe: scaladsl.Recipe = setupSimpleRecipe("recipename")
    baasClient.addRecipe(originalRecipe)
  }

  "Happy flow simple recipe BAAS" ignore {
    val recipeName = "simpleRecipe" + UUID.randomUUID().toString
    val recipe = setupSimpleRecipe(recipeName)

    baasClient.addRecipe(recipe)

    val requestId = UUID.randomUUID().toString

    baasClient.bake(recipeName, requestId)

    val sensoryEventStatusResponse: SensoryEventStatus =
      baasClient.handleEvent(recipeName, requestId, InitialEvent("initialIngredient"), EventConfirmation.COMPLETED)
    sensoryEventStatusResponse shouldBe SensoryEventStatus.Completed

    val processState: ProcessState = baasClient.getState(recipeName, requestId)

    processState.ingredients.keys should contain("initialIngredient")
    processState.ingredients.keys should contain("interactionOneIngredient")

    val events = baasClient.getEvents(recipeName, requestId)

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
