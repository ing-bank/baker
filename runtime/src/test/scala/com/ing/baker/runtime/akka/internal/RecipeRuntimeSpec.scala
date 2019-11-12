package com.ing.baker.runtime.akka.internal

import java.util.UUID

import com.ing.baker.il
import com.ing.baker.il.IngredientDescriptor
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.scaladsl.RecipeInstanceState
import com.ing.baker.types.Value
import org.mockito.Mockito._
import org.scalatest.mockito.MockitoSugar
import org.scalatest.{Matchers, WordSpecLike}

class RecipeRuntimeSpec extends WordSpecLike with Matchers with MockitoSugar {
  "The recipe runtime" should {
    "return a ProcessID ingredient if necessary" in {
      val processId = UUID.randomUUID().toString
      val notRelevant = Map.empty[String, Value]
      val mockTransition = mock[InteractionTransition]
      val mockState = mock[RecipeInstanceState]
      when(mockTransition.predefinedParameters).thenReturn(notRelevant)
      // annotating an interaction with @ProcessId will include an extra ingredient in the list of required ingredients
      //TODO how to turn the String into Type?
//      when(mockTransition.requiredIngredients).thenReturn(Seq(IngredientDescriptor(il.processIdName, processId)))
      when(mockState.ingredients).thenReturn(notRelevant)
      when(mockState.recipeInstanceId).thenReturn(processId)
      RecipeRuntime.createInteractionInput(mockTransition, mockState)

      //TODO verify the id matches the processId
    }
  }
}