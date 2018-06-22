package com.ing.baker.recipe.commonserialize

import java.util.UUID

import com.ing.baker.BakerRuntimeTestBase
import com.ing.baker.TestRecipe._
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


class SerializerSpec extends BakerRuntimeTestBase {
  override def actorSystemName: String = "SerializerSpec"

  "BAAS" when {
    "converting to the common serialize recipe" in {
      val scalaDSLRecipe: scaladsl.Recipe = getRecipe("commonSerializeRecipe")
      val commonSerializeRecipe: commonserialize.Recipe = new Recipe(scalaDSLRecipe)

      commonSerializeRecipe shouldBe scalaDSLRecipe
    }

    "Serialize and deserialize a common recipe" in {
      withKryo { kryo =>
        val originalRecipe: Recipe = new Recipe(getRecipe("name"))

        val serializedRecipe: Array[Byte] = kryo.toBytesWithClass(originalRecipe)
        val deserializedRecipe: Recipe = kryo.fromBytes(serializedRecipe).asInstanceOf[Recipe]

        deserializedRecipe shouldBe originalRecipe
      }
    }

    "Serialize and deserialize a recipe" in {
      withKryo { kryo =>
        resetMocks
        setupMockResponse()

        val originalRecipe: Recipe = new Recipe(getRecipe("name"))

        val serializedRecipe: Array[Byte] = kryo.toBytesWithClass(originalRecipe)
        val deserializedRecipe: Recipe = kryo.fromBytes(serializedRecipe).asInstanceOf[Recipe]

        val compiledRecipeOriginal: CompiledRecipe = RecipeCompiler.compileRecipe(originalRecipe)
        val compiledRecipeDeserialized: CompiledRecipe = RecipeCompiler.compileRecipe(deserializedRecipe)

        compiledRecipeDeserialized.getRecipeVisualization shouldBe compiledRecipeOriginal.getRecipeVisualization

        val (baker, recipeId) = setupBakerWithRecipe(deserializedRecipe, mockImplementations)

        val processId = UUID.randomUUID().toString
        baker.bake(recipeId, processId)

        verifyZeroInteractions(testInteractionOneMock)

        val received = baker.processEvent(processId, InitialEvent(initialIngredientValue))
        received shouldBe SensoryEventStatus.Completed

        verify(testInteractionTwoMock).apply(initialIngredientValue)
        verify(testProvidesNothingInteractionMock).apply(initialIngredientValue)
        verify(testSieveInteractionMock).apply(processId.toString, initialIngredientValue)
        verify(testInteractionOneMock).apply(processId.toString, initialIngredientValue)
      }
    }
  }
}
