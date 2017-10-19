package com.ing.baker.recipe.commonserialize

import java.util.UUID

import com.ing.baker.TestRecipeHelper
import com.ing.baker.TestRecipeHelper.InitialEvent
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.core.{Baker, SensoryEventStatus}
import com.twitter.chill.{KryoPool, ScalaKryoInstantiator}
import org.mockito.Mockito.{verify, verifyZeroInteractions}

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
//        println(compiledRecipeDeserialized.getRecipeVisualization)
        compiledRecipeDeserialized.getRecipeVisualization shouldBe compiledRecipeOriginal.getRecipeVisualization


        resetMocks
        val baker = new Baker(mockImplementations)

        val recipeHandler = baker.addRecipe(compiledRecipeDeserialized)

        val processId = UUID.randomUUID().toString
        recipeHandler.bake(processId)

        verifyZeroInteractions(testInteractionOneMock)

        val received = recipeHandler.handleEvent(processId, InitialEvent(initialIngredientValue))
        received shouldBe SensoryEventStatus.Completed

        verify(testInteractionTwoMock).apply(initialIngredientValue)
        verify(testProvidesNothingInteractionMock).apply(initialIngredientValue)
        verify(testSieveInteractionMock).apply(processId.toString, initialIngredientValue)
        verify(testInteractionOneMock).apply(processId.toString, initialIngredientValue)

      }
    }
  }

  private def withKryo(f: KryoPool => Unit): Unit = {
    val kryoPool = KryoPool.withByteArrayOutputStream(1, new ScalaKryoInstantiator)
    f(kryoPool)
  }
}
