package com.ing.baker.recipe.commonserialize

import java.util.UUID

import com.ing.baker.TestRecipeHelper
import com.ing.baker.TestRecipeHelper.{InitialEvent, OptionalIngredientInteraction}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.commonserialize.SerializerSpec.withKryo
import com.ing.baker.recipe.scaladsl
import com.ing.baker.recipe.commonserialize
import com.ing.baker.runtime.core.{Baker, SensoryEventStatus}
import com.twitter.chill.{KryoPool, ScalaKryoInstantiator}
import org.mockito.Mockito.{verify, verifyZeroInteractions}

object SerializerSpec {
  private def withKryo(f: KryoPool => Unit): Unit = {
    val kryoPool = KryoPool.withByteArrayOutputStream(1, new ScalaKryoInstantiator)
    f(kryoPool)
  }
}


class SerializerSpec extends TestRecipeHelper {
  override def actorSystemName: String = "SerializerSpec"

  "BAAS" when {
    "converting to the common serialize recipe" in {
      val scalaDSLRecipe: scaladsl.Recipe = getComplexRecipe("commonSerializeRecipe");
      val commonSerializeRecipe: commonserialize.Recipe = new Recipe(scalaDSLRecipe)

      commonSerializeRecipe shouldBe scalaDSLRecipe
    }

    "Serialize and deserialize a common recipe" in {
      withKryo { kryo =>
        val orignalRecipe: Recipe = new Recipe(getComplexRecipe("name"))

        val serializedRecipe: Array[Byte] = kryo.toBytesWithClass(orignalRecipe)
        val deserializedRecipe: Recipe = kryo.fromBytes(serializedRecipe).asInstanceOf[Recipe]

        deserializedRecipe shouldBe orignalRecipe
      }
    }

    "Serialize and deserialze a recipe" in {
      withKryo { kryo =>
        resetMocks
        setupMockResponse

        val orignalRecipe: Recipe = new Recipe(getComplexRecipe("name"))

        val serializedRecipe: Array[Byte] = kryo.toBytesWithClass(orignalRecipe)
        val deserializedRecipe: Recipe = kryo.fromBytes(serializedRecipe).asInstanceOf[Recipe]


        val compiledRecipeOriginal: CompiledRecipe = RecipeCompiler.compileRecipe(orignalRecipe);
        val compiledRecipeDeserialized: CompiledRecipe = RecipeCompiler.compileRecipe(deserializedRecipe);
        compiledRecipeDeserialized.getRecipeVisualization shouldBe compiledRecipeOriginal.getRecipeVisualization

//        println(compiledRecipeDeserialized.getPetriNetVisualization)

        val recipeHandler = setupBakerWithRecipe(deserializedRecipe, mockImplementations)

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
}
