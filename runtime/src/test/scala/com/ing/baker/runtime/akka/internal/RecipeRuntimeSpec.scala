package com.ing.baker.runtime.akka.internal

import java.util.UUID

import com.ing.baker.il.IngredientDescriptor
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.scaladsl.RecipeInstanceState
import com.ing.baker.types.Value
import com.ing.baker.{il, types}
import org.mockito.Mockito._
import org.scalatest.{Matchers, WordSpecLike}
import org.scalatestplus.mockito.MockitoSugar

class RecipeRuntimeSpec extends WordSpecLike with Matchers with MockitoSugar {
  "The recipe runtime" should {
    "provide a ProcessID ingredient to an interaction if required" in {
      val processId = UUID.randomUUID().toString
      val irrelevant = Map.empty[String, Value]
      val mockTransition = mock[InteractionTransition]
      val mockState = mock[RecipeInstanceState]

      when(mockTransition.predefinedParameters).thenReturn(irrelevant)
      when(mockState.ingredients).thenReturn(irrelevant)
      //the @ProcessId annotation will include an extra ingredient in the list of required ingredients
      when(mockTransition.requiredIngredients).thenReturn(Seq(IngredientDescriptor(il.processIdName, types.CharArray)))
      //in V3, process id from V1 and V2 is now called a recipe instance id
      when(mockState.recipeInstanceId).thenReturn(processId)

      //this call would fail without the fix
      RecipeRuntime.createInteractionInput(mockTransition, mockState)
    }
  }
}