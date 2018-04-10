package com.ing.baker.runtime.actor.interactions

import com.ing.baker.il.IngredientDescriptor
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.core.interations.{InteractionImplementation, InteractionManager}
import com.ing.baker.types.PrimitiveType
import org.mockito.Mockito.when
import org.scalatest.mockito.MockitoSugar
import org.scalatest.{Matchers, WordSpecLike}

class InteractionManagerSpec extends WordSpecLike with Matchers with MockitoSugar {

  "hasCompatibleImplementation" should {
    "return  true" when {
      "interactionImplementation found" in {
        val interactionImplementation = mock[InteractionImplementation]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.inputTypes).thenReturn(Seq(PrimitiveType(classOf[Int])))

        val interactionManager: InteractionManager = new InteractionManager(Seq(interactionImplementation))
        val interactionTransition = mock[InteractionTransition[_]]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", PrimitiveType(classOf[Int]))
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        interactionManager.hasCompatibleImplementation(interactionTransition) should equal(true)
      }

      "multiple interactionImplementations found" in {
        val interactionImplementation1 = mock[InteractionImplementation]
        when(interactionImplementation1.name).thenReturn("InteractionName")
        when(interactionImplementation1.inputTypes).thenReturn(Seq(PrimitiveType(classOf[Int])))

        val interactionImplementation2 = mock[InteractionImplementation]
        when(interactionImplementation2.name).thenReturn("InteractionName2")
        when(interactionImplementation2.inputTypes).thenReturn(Seq(PrimitiveType(classOf[Int])))

        val interactionManager: InteractionManager = new InteractionManager(Seq(interactionImplementation1, interactionImplementation2))
        val interactionTransition = mock[InteractionTransition[_]]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", PrimitiveType(classOf[Int]))
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        interactionManager.hasCompatibleImplementation(interactionTransition) should equal(true)
      }
    }

    "return false" when {
      "interactionImplementation has wrong ingredient input type" in {
        val interactionImplementation = mock[InteractionImplementation]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.inputTypes).thenReturn(Seq(PrimitiveType(classOf[Int])))

        val interactionManager: InteractionManager = new InteractionManager(Seq(interactionImplementation))
        val interactionTransition = mock[InteractionTransition[_]]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", PrimitiveType(classOf[String]))
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        interactionManager.hasCompatibleImplementation(interactionTransition) should equal(false)
      }

      "interactionImplementation has extra ingredient input types" in {
        val interactionImplementation = mock[InteractionImplementation]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.inputTypes).thenReturn(Seq(PrimitiveType(classOf[Int]), PrimitiveType(classOf[String])))

        val interactionManager: InteractionManager = new InteractionManager(Seq(interactionImplementation))
        val interactionTransition = mock[InteractionTransition[_]]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", PrimitiveType(classOf[Int]))
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor))

        interactionManager.hasCompatibleImplementation(interactionTransition) should equal(false)
      }

      "interactionImplementation has not enough ingredient input types" in {
        val interactionImplementation = mock[InteractionImplementation]
        when(interactionImplementation.name).thenReturn("InteractionName")
        when(interactionImplementation.inputTypes).thenReturn(Seq(PrimitiveType(classOf[Int])))

        val interactionManager: InteractionManager = new InteractionManager(Seq(interactionImplementation))
        val interactionTransition = mock[InteractionTransition[_]]
        when(interactionTransition.originalInteractionName).thenReturn("InteractionName")
        val ingredientDescriptor: IngredientDescriptor = IngredientDescriptor("ingredientName", PrimitiveType(classOf[Int]))
        val ingredientDescriptor2: IngredientDescriptor = IngredientDescriptor("ingredientName2", PrimitiveType(classOf[String]))
        when(interactionTransition.requiredIngredients).thenReturn(Seq(ingredientDescriptor, ingredientDescriptor2))

        interactionManager.hasCompatibleImplementation(interactionTransition) should equal(false)
      }

      "empty interaction seq" in {
        val interactionManager: InteractionManager = new InteractionManager(Seq.empty)

        val interactionTransition: InteractionTransition[_] = mock[InteractionTransition[_]]
        interactionManager.hasCompatibleImplementation(interactionTransition) should equal(false)
      }
    }
  }
}
