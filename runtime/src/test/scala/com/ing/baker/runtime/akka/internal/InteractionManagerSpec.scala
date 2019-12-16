package com.ing.baker.runtime.akka.internal

import com.ing.baker.il.IngredientDescriptor
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.baker.types
import com.ing.baker.types.Type
import org.mockito.Mockito.when
import org.scalatest.{Matchers, WordSpecLike}
import org.scalatestplus.mockito.MockitoSugar

class InteractionManagerLocalSpec extends WordSpecLike with Matchers with MockitoSugar {
  "getImplementation" should {
    "return Some" when {
      "an interaction implementation is available" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(types.Int32))

        val interactionManager: InteractionManagerLocal = new InteractionManagerLocal(Seq(interactionImplementation))
        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        interactionManager.getImplementation(interactionTransition) should equal(Some(interactionImplementation))
      }

      "multiple interaction implementations are available" in {
        val interactionImplementation1 = mock[InteractionInstance]
        when(interactionImplementation1.name).thenReturn("InteractionName")
        when(interactionImplementation1.input).thenReturn(Seq(types.Int32))

        val interactionImplementation2 = mock[InteractionInstance]
        when(interactionImplementation2.name).thenReturn("InteractionName2")
        when(interactionImplementation2.input).thenReturn(Seq(types.Int32))

        val interactionManager: InteractionManagerLocal = new InteractionManagerLocal(Seq(interactionImplementation1, interactionImplementation2))
        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        interactionManager.getImplementation(interactionTransition) should equal(Some(interactionImplementation1))
      }

      "two implementations with the same correct name but only one has the correct input types" in {
        val interactionImplementation1 = mock[InteractionInstance]
        when(interactionImplementation1.name).thenReturn("InteractionName")
        when(interactionImplementation1.input).thenReturn(Seq.empty[Type])

        val interactionImplementation2 = mock[InteractionInstance]
        when(interactionImplementation2.name).thenReturn("InteractionName")
        when(interactionImplementation2.input).thenReturn(Seq(types.Int32))

        val interactionManager: InteractionManagerLocal = new InteractionManagerLocal(Seq(interactionImplementation1, interactionImplementation2))
        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        interactionManager.getImplementation(interactionTransition) should equal(Some(interactionImplementation2))
      }
    }

    "return None" when {
      "an interaction implementation has a wrong name" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(types.Int32))

        val interactionManager: InteractionManagerLocal = new InteractionManagerLocal(Seq(interactionImplementation))
        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("WrongInteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        interactionManager.getImplementation(interactionTransition) should equal(None)
      }

      "an interaction implementation has a wrong ingredient input type" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(types.Int32))

        val interactionManager: InteractionManagerLocal = new InteractionManagerLocal(Seq(interactionImplementation))
        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.CharArray)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        interactionManager.getImplementation(interactionTransition) should equal(None)
      }

      "an interaction implementation has extra ingredient input types" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(types.Int32, types.CharArray))

        val interactionManager: InteractionManagerLocal = new InteractionManagerLocal(Seq(interactionImplementation))
        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        interactionManager.getImplementation(interactionTransition) should equal(None)
      }

      "an interaction implementation has not enough ingredient input types" in {
        val interactionImplementation = mock[InteractionInstance]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.input).thenReturn(Seq(types.Int32))

        val interactionManager: InteractionManagerLocal = new InteractionManagerLocal(Seq(interactionImplementation))
        val interactionTransition = mock[InteractionTransition]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", types.Int32)
        val ingredientDescriptor2: IngredientDescriptor = IngredientDescriptor("ingredientName2", types.CharArray)
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor, ingredientDescriptor2))

        interactionManager.getImplementation(interactionTransition) should equal(None)
      }

      "empty interaction seq" in {
        val interactionManager: InteractionManagerLocal = new InteractionManagerLocal(Seq.empty)

        val interactionTransition: InteractionTransition = mock[InteractionTransition]
        interactionManager.getImplementation(interactionTransition) should equal(None)
      }
    }
  }
}
