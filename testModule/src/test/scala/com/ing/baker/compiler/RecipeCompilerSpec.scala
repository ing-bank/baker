//package com.ing.baker.compiler
//
//import com.ing.baker._
//import com.ing.baker.compiledRecipe.CompiledRecipe
//import com.ing.baker.recipe.common.Recipe
//import com.ing.baker.recipe.scaladsl.{InteractionDescriptorFactory, SRecipe}
//
//import scala.concurrent.duration._
//import scala.language.postfixOps
//
//class RecipeCompilerSpec extends TestRecipeHelper {
//
//
//  implicit val timeout: FiniteDuration = 10 seconds
//
//  before {
//    resetMocks
//  }
//
//  "The RecipeCompiler after compilation" should {
//
//    "should not contain errors if compiling a valid recipe" in {
//      val recipe: Recipe = getComplexRecipe("ValidRecipe")
//      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
//      System.out.println(compiledRecipe.getRecipeVisualization)
//      //For now all missing implementation errors are provided so they are filtered out
//      compiledRecipe.validationErrors.filterNot(s => s.startsWith("No implementation provided for interaction")) shouldBe List.empty
//
//    }
//
//    "give a List of missing ingredients if an interaction has an ingredient that is not provided by any other event or interaction" in {
//      val recipe = SRecipe(name = "NonProvidedIngredient",
//                          interactions = Seq(InteractionDescriptorFactory[InteractionOne]),
//                          events = Set.empty)
//
//      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
//      compiledRecipe.validationErrors should contain ("Ingredient 'initialIngredient' for interaction 'interface com.ing.baker.InteractionOne:apply' is not provided by any event or interaction")
//    }
//
//    //"This should be tested in the runtime when the Baker is initilaized, not in the recipe compilation")
//
//    "give a list of wrong interactions if an event of an interaction does not match it's return type" in {
//      val recipe = SRecipe(
//        name = "NonMatchingReturnTypeTest",
//        interactions = Seq(
//          InteractionDescriptorFactory[NonMatchingReturnTypeInteraction]
//        ),
//        events = Set(classOf[InitialEvent])
//      )
//      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
//      compiledRecipe.validationErrors should contain ("Event class: class com.ing.baker.EventFromInteractionTwo is not assignable to return type: class java.lang.String for interaction: NonMatchingReturnTypeInteraction")
//    }
//
//    "give a list of wrong ingredients if an predefined ingredient is of the wrong type" in {
//      val recipe = SRecipe(
//        name = "WrongGivenIngredient",
//        interactions = Seq(
//          InteractionDescriptorFactory[InteractionOne]
//                .withRequiredEvent[InitialEvent]
//                .withPredefinedIngredients(("initialIngredient", Integer.valueOf(12)))
//        ),
//        events = Set(classOf[InitialEvent])
//      )
//      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
//      compiledRecipe.validationErrors should contain ("Predefined argument 'initialIngredient' is not of type: class java.lang.String on interaction: 'InteractionOne'")
//    }
//
//    "give a list of wrong ingredients if an predefined ingredient is not needed by the interaction" in {
//      val recipe = SRecipe(
//        name = "WrongGivenIngredient",
//        interactions = Seq(
//          InteractionDescriptorFactory[InteractionOne]
//            .withPredefinedIngredients(("WrongIngredient", null))
//        ),
//        events = Set(classOf[InitialEvent])
//      )
//      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
//      compiledRecipe.validationErrors should contain ("Predefined argument 'WrongIngredient' is not defined on interaction: 'InteractionOne'")
//    }
//  }
//}
