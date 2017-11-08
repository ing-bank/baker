package com.ing.baker.baas

import akka.actor.ActorSystem
import com.ing.baker.TestRecipeHelper
import com.ing.baker.TestRecipeHelper.{initialEvent, interactionOne}
import com.ing.baker.baas.http.BAASAPI
import com.ing.baker.recipe.{commonserialize, scaladsl}

import scala.concurrent.Await
import scala.concurrent.duration._

class BAASSpec extends TestRecipeHelper {
  override def actorSystemName: String = "BAASSpec"

  //Startup a empty BAAS cluster
  val baasAPI: BAASAPI = new BAASAPI(new BAAS())(ActorSystem("BAASAPIActorSystem"))
  Await.result(baasAPI.start(), 10 seconds)

  //Start a BAAS API
  val baasClient: BAASClient = new BAASClient("http://localhost", 8081)


  "Serialize and deserialize a common recipe" in {
    val originalRecipe: commonserialize.Recipe = new commonserialize.Recipe(getComplexRecipe("name"))
    val serializedRecipe = BAAS.serializeRecipe(originalRecipe)
    val deserializedRecipe = BAAS.deserializeRecipe(serializedRecipe)

    deserializedRecipe shouldBe originalRecipe
  }

  "Send recipe to the BAAS API" ignore {
    val originalRecipe: scaladsl.Recipe = getComplexRecipe("recipename")
    baasClient.addRecipe(originalRecipe)
  }

  "Get all recipe names from the BAAS API" ignore {
    val originalRecipe: scaladsl.Recipe = getComplexRecipe("recipename")
    baasClient.addRecipe(originalRecipe)
  }

  "Add a implementation to the BAAS API" ignore {
    baasClient.addImplementation(InteractionOne());
  }

  case class InteractionOne(name: String = "InteractionOne") {
    def apply(processId: String, initialIngredient: String): String = initialIngredient
  }

  "Add implementations and recipe to BAASAPI" in {
    val recipe = scaladsl.Recipe("simpleRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

    baasClient.addImplementation(InteractionOne());
    baasClient.addRecipe(recipe)
  }
}
