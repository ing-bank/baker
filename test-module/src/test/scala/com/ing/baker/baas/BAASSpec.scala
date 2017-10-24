package com.ing.baker.baas

import com.ing.baker.TestRecipeHelper
import com.ing.baker.recipe.commonserialize.Recipe

class BAASSpec extends TestRecipeHelper {
  override def actorSystemName: String = "BAASSpec"

  "Serialize and deserialize a common recipe" in {
    val originalRecipe: Recipe = new Recipe(getComplexRecipe("name"))
    val serializedRecipe = BAAS.serializeRecipe(originalRecipe)
    val deserializedRecipe = BAAS.deserializeRecipe(serializedRecipe)

    deserializedRecipe shouldBe originalRecipe
  }
}
