//package com.ing.baker.runtime.core
//
//import com.ing.baker._
//import com.ing.baker.compiler.RecipeCompiler
//import com.ing.baker.core.{BakerException, NonSerializableException, RecipeValidationException}
//import com.ing.baker.recipe.scaladsl.{InteractionDescriptorFactory, SRecipe, SieveDescriptorFactory}
//
//import scala.concurrent.duration._
//import scala.language.postfixOps
//
//class BakerSetupSpec extends TestRecipeHelper {
//
//
//  implicit val timeout: FiniteDuration = 10 seconds
//
//  before {
//    resetMocks
//  }
//
//  "The Baker execution engine during setup" should {
//
//    "throw an RecipeValidationException if an invalid recipe is given" in {
//      val recipe = SRecipe(name = "NonProvidedIngredient",
//                          interactions = Seq(InteractionDescriptorFactory[InteractionOne]),
//                          events = Set.empty)
//
//      a[RecipeValidationException] should be thrownBy {
//        new Baker(
//          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
//          implementations = mockImplementations,
//          actorSystem = defaultActorSystem)
//      }
//    }
//
//    "throw a BakerException if a sieve does not have a default constructor" in {
//      val recipe = SRecipe(name = "SieveWithoutDefaultConstructor",
//        interactions = Seq(SieveDescriptorFactory[SieveInteractionWithoutDefaultConstructor]),
//        events = Set(classOf[InitialEvent]))
//
//      intercept[BakerException] {
//        new Baker(
//          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
//          implementations = Map.empty,
//          actorSystem = defaultActorSystem)
//      } should have('message("No default constructor found for Sieve: 'class com.ing.baker.SieveInteractionWithoutDefaultConstructor'"))
//    }
//
//    "throw an BakerException if a recipe does not provide an implementation for an interaction" in {
//      val recipe = SRecipe(name = "MissingImplementation",
//        interactions = Seq(InteractionDescriptorFactory[InteractionOne]),
//        events = Set(classOf[InitialEvent]))
//
//      intercept[BakerException] {
//        new Baker(
//          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
//          implementations = Map.empty,
//          actorSystem = defaultActorSystem)
//      } should have('message("No implementation provided for interaction: interface com.ing.baker.InteractionOne"))
//    }
//
//    "throw NonSerializableException with the list of ingredient serialization validation errors for Ingredients provided by Interactions" in {
//
//      val recipe = SRecipe(
//        name = "NonSerializableIngredientTest",
//        interactions = Seq(InteractionDescriptorFactory[NonSerializableIngredientInteraction]),
//        events = Set(classOf[InitialEvent])
//      )
//
//      intercept[NonSerializableException] {
//        new Baker(
//          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
//          implementations = mockImplementations,
//          actorSystem = defaultActorSystem)
//      } should have('message("Ingredient nonSerializableIngredient of class com.ing.baker.NonSerializableObject is not serializable by akka"))
//
//    }
//
//    "throw NonSerializableException with the list of ingredient serialization validation errors for Ingredients provided by Events" in {
//
//      val recipe = SRecipe(
//        name = "NonSerializableIngredientFromEventTest",
//        interactions = Seq(),
//        events = Set(classOf[EventWithANonSerializableIngredient])
//      )
//
//      intercept[NonSerializableException] {
//        new Baker(
//          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
//          implementations = mockImplementations,
//          actorSystem = defaultActorSystem)
//      } should have('message("Ingredient nonSerializableObject of class com.ing.baker.NonSerializableObject is not serializable by akka"))
//
//    }
//
//
//    //TODO ad this validation when starting up the baker runtime
//    "throw NonSerializableException with a list of non serializable events if an event is not Serializable" ignore {
//
//      val recipe = SRecipe(
//        name = "NonSerializableEventTest",
//        interactions = Seq(
//          InteractionDescriptorFactory[NonSerializableEventInteraction]
//        ),
//        events = Set(classOf[InitialEvent])
//      )
//
//      intercept[NonSerializableException] {
//        new Baker(
//          compiledRecipe = RecipeCompiler.compileRecipe(recipe),
//          implementations = mockImplementations,
//          actorSystem = defaultActorSystem)
//      } should have('message("Event class: class com.ing.baker.NonSerializableObject does not extend from com.ing.baker.api.Event"))
//    }
//
//  }
//}
