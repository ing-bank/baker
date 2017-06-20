package com.ing.baker.runtime.recipe.transitions

import com.ing.baker.recipe.annotations.RequiresIngredient
import com.ing.baker.runtime.ingredient_extractors.CompositeIngredientExtractor
import org.scalatest.{FunSpec, ShouldMatchers}

object ActionExecutingTransitionSpec {

  trait SampleIngredient {
    def action1(@RequiresIngredient("overriddenName") arg1: String): Unit
  }

  class SampleIngredientImpl extends SampleIngredient {
    override def action1(arg1: String): Unit = {}
  }
}

class ActionExecutingTransitionSpec extends FunSpec with ShouldMatchers {

  val ingredientExtractor = new CompositeIngredientExtractor()

//  describe("ActionExecutingTransition") {
//    it("should understand @RequiresIngredient arguments of actions in scala classes") {
//
//      val impl = new SampleIngredientImpl()
//
//      val actionExecutingTransition =
//        new InteractionTransition[SampleIngredient](interactionClass = classOf[SampleIngredient],
//                                                    interactionProvider = () => impl,
//                                                    interactionMethod = "action1",
//                                                    interactionName = "action1",
//                                                    predefinedParameters = Map.empty,
//                                                    overriddenIngredientNames = Map.empty,
//                                                    maximumInteractionCount = None,
//                                                    overriddenOutputIngredientName = null,
//                                                    failureStrategy = InteractionFailureStrategy.BlockInteraction,
//                                                    ingredientExtractor = ingredientExtractor)
//
//      actionExecutingTransition.inputFieldNames should equal(Array("overriddenName"))
//    }
//
//    it("should understand @RequiresIngredient arguments of actions in java classes") {
//
//      val impl = new SampleIngredientImpl()
//
//      val actionExecutingTransition =
//        InteractionTransition[SampleIngredient](interactionClass = classOf[SampleIngredient],
//                                                interactionProvider = () => impl,
//                                                interactionMethod = "action1",
//                                                interactionName = "action1",
//                                                predefinedParameters = Map.empty,
//                                                overriddenIngredientNames = Map.empty,
//                                                maximumInteractionCount = None,
//                                                overriddenOutputIngredientName = null,
//                                                failureStrategy = InteractionFailureStrategy.BlockInteraction,
//                                                ingredientExtractor = ingredientExtractor)
//
//      actionExecutingTransition.inputFieldNames should equal(Array("overriddenName"))
//    }
//
//    it("should use the overridden ingredient name for the parameters") {
//
//      val impl = new SampleIngredientImpl()
//
//      val actionExecutingTransition =
//        InteractionTransition[SampleIngredient](interactionClass = classOf[SampleIngredient],
//                                                interactionProvider = () => impl,
//                                                interactionMethod = "action1",
//                                                interactionName = "aInteraction",
//                                                predefinedParameters = Map.empty,
//                                                overriddenIngredientNames =
//                                                  Map("overriddenName" -> "secondOverriddenName"),
//                                                maximumInteractionCount = None,
//                                                overriddenOutputIngredientName = null,
//                                                failureStrategy = InteractionFailureStrategy.BlockInteraction,
//                                                ingredientExtractor = ingredientExtractor)
//
//      actionExecutingTransition.inputFieldNames should equal(Array("secondOverriddenName"))
//    }
//  }

}
