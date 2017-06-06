//package com.ing.baker.newrecipe.javadsl
//
//
//import com.ing.baker.recipe.annotations.{ProvidesIngredient, RequiresIngredient}
//import org.scalatest.{Matchers, WordSpecLike}
//import org.scalatest.mock.MockitoSugar
//
//class InteractionSpec extends WordSpecLike with Matchers with MockitoSugar {
//  "an Interaction" when {
//    "Being created from the javadsl" should {
//      "have a correct output type" in {
//        trait SimpleInteraction extends Interaction{
//          @ProvidesIngredient("originalIngredient")
//          def action1(@RequiresIngredient("overriddenName") arg1: String): Int
//        }
//
//        case object SimpleInteractionImpl extends SimpleInteraction {
//          override def action1(arg1: String): Int = 10
//        }
//
//        println(SimpleInteractionImpl.toString)
//
//      }
//    }
//  }
//
//}
