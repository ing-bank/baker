package com.ing.baker.baas

import java.util.UUID

import akka.actor.ActorSystem
import com.ing.baker.baas.BAASSpec.{InteractionOne, _}
import com.ing.baker.baas.http.GetStateHTTResponse
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.common.ProvidesIngredient
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Ingredients, Interaction, processId}
import com.ing.baker.recipe.{commonserialize, scaladsl}
import com.ing.baker.runtime.core.{Baker, SensoryEventStatus}
import org.scalatest.{Matchers, WordSpecLike}

import scala.concurrent.duration._

class BAASSpec extends WordSpecLike with Matchers {
  def actorSystemName: String = "BAASSpec"

  //Startup a empty BAAS cluster
//  val baasAPI: BAASAPI = new BAASAPI(new BAAS())(ActorSystem("BAASAPIActorSystem"))
//  Await.result(baasAPI.start(), 10 seconds)

  //Start a BAAS API
  val baasClient: BAASClient = new BAASClient("localhost", 8081)


  "Serialize and deserialize a common recipe" in {
    val originalRecipe: commonserialize.Recipe = new commonserialize.Recipe(setupSimpleRecipe("name"))
    val serializedRecipe = BAAS.serializeRecipe(originalRecipe)
    val deserializedRecipe = BAAS.deserializeRecipe(serializedRecipe)

    deserializedRecipe shouldBe originalRecipe
  }

  "Send recipe to the BAAS API" ignore {
    val originalRecipe: scaladsl.Recipe = setupSimpleRecipe("recipename")
    baasClient.addRecipe(originalRecipe)
  }

  "Get all recipe names from the BAAS API" ignore {
    val originalRecipe: scaladsl.Recipe = setupSimpleRecipe("recipename")
    baasClient.addRecipe(originalRecipe)
  }

  "Add a implementation to the BAAS API" ignore {
    baasClient.addImplementation(InteractionOne);
  }

  "Happy flow simple recipe BAAS" in {
    val recipeName = "simpleRecipe" + UUID.randomUUID().toString
    val recipe = setupSimpleRecipe(recipeName)

    baasClient.addImplementation(InteractionOne())

    baasClient.addRecipe(recipe)

    val requestId = UUID.randomUUID().toString

    baasClient.bake(recipeName, requestId)

    val sensoryEventStatusResponse: SensoryEventStatus = baasClient.handleEvent(recipeName, requestId, InitialEvent("initialIngredient"))
    sensoryEventStatusResponse shouldBe SensoryEventStatus.Completed

    val requestState: GetStateHTTResponse = baasClient.getState(recipeName, requestId)

    requestState.processState.ingredients.keys should contain("initialIngredient")
    requestState.processState.ingredients.keys should contain("interactionOneIngredient")
//    println(s"procesState : ${requestState.processState}")
//    println(s"visualState : ${requestState.visualState}")
  }

  "Happy flow simple recipe baker" ignore {
    implicit val timeout = 30 seconds

    val recipeName = "simpleRecipe" + UUID.randomUUID().toString
    val recipe = setupSimpleRecipe(recipeName)

    val baker = new Baker()(ActorSystem("testActorSystem"))
    baker.addInteractionImplementation(InteractionOne())

    val recipeHandler = baker.addRecipe(RecipeCompiler.compileRecipe(recipe))

    val requestId = UUID.randomUUID().toString

    recipeHandler.bake(requestId)

    val sensoryEventStatusResponse: SensoryEventStatus =
      recipeHandler.handleEvent(requestId, InitialEvent("initialIngredient"))
    sensoryEventStatusResponse shouldBe SensoryEventStatus.Completed

    val visualState = recipeHandler.getVisualState(requestId)
    println(s"visualState : $visualState")
  }
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

  def setupSimpleRecipe(name: String): scaladsl.Recipe = {
    scaladsl.Recipe(name)
      .withInteraction(interactionOne)
      .withSensoryEvent(initialEvent)
  }
}
