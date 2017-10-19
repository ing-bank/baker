package com.ing.baker.recipe.commonserialize

import com.ing.baker.TestRecipeHelper
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.core.Baker
import com.twitter.chill.{KryoPool, ScalaKryoInstantiator}

class SerializerSpec extends TestRecipeHelper {
  override def actorSystemName: String = "SerializerSpec"

  "Can serialize a recipe" when {
    "converted to the commonserializer format" in {
      withKryo { kryo =>
        val orignalRecipe: Recipe = new Recipe(getComplexRecipe("name"))

        val compiledRecipeOriginal: CompiledRecipe = RecipeCompiler.compileRecipe(orignalRecipe);
//        println(compiledRecipeOriginal.getRecipeVisualization)

        val serializedRecipe: Array[Byte] = kryo.toBytesWithClass(orignalRecipe)
        val deserializedRecipe: Recipe = kryo.fromBytes(serializedRecipe).asInstanceOf[Recipe]

        val compiledRecipeDeserialized: CompiledRecipe = RecipeCompiler.compileRecipe(orignalRecipe);
        println(compiledRecipeDeserialized.getRecipeVisualization)


        val baker = new Baker(mockImplementations)
        val recipeHandler = baker.addRecipe(compiledRecipeDeserialized)

        compiledRecipeDeserialized.getRecipeVisualization shouldBe compiledRecipeOriginal.getRecipeVisualization

//        kryo.fromBytes(kryo.toBytesWithClass(onboardingRecipe)) shouldBe onboardingRecipe
      }
    }
  }

  private def withKryo(f: KryoPool => Unit): Unit = {
    val kryoPool = KryoPool.withByteArrayOutputStream(1, new ScalaKryoInstantiator)
    f(kryoPool)
  }
}
