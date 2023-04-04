package com.ing.baker.compiler

import com.ing.baker.il.petrinet.InteractionTransition

import java.util.Optional
import com.ing.baker.il.{CompiledRecipe, ValidationSettings, checkpointEventInteractionPrefix}
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.{TestRecipeJava, common}
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilDeadline
import com.ing.baker.recipe.scaladsl._
import com.ing.baker.types._
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpecLike

import scala.concurrent.duration._
import scala.language.postfixOps
import scala.collection.immutable.Seq

class RecipeCompilerSpec extends AnyWordSpecLike with Matchers {

  "The recipe compiler" should {

    "not have validation errors for a valid recipe" in {
      val recipe: Recipe = getRecipe("ValidRecipe")
      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe List.empty

      // dumpToFile("TestRecipe.svg", compiledRecipe.getVisualRecipeAsSVG)
    }

    "add the exhausted retry event to the interaction event output list if defined" in {
      val exhaustedEvent = Event("RetryExhausted")
      val recipe = Recipe("RetryExhaustedRecipe")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withFailureStrategy(
          InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
            .withInitialDelay(10 milliseconds)
            .withUntil(Some(UntilDeadline(10 seconds)))
            .withFireRetryExhaustedEvent(exhaustedEvent)
            .build()))

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)

      compiledRecipe.allEvents.map(_.name) should contain(exhaustedEvent.name)
    }

    "generate the same id for the same recipe" in {
      val first = RecipeCompiler.compileRecipe(getRecipe("ValidRecipe")).recipeId
      (1 to 10)
        .map(_ => getRecipe("ValidRecipe"))
        .map(RecipeCompiler.compileRecipe(_).recipeId)
        .foreach(_ shouldBe first)
    }

    "generate different ids for recipes with changes on transitions other than the name" in {
      val input = Ingredient[Int]("ingredient")
      val output = Event("event", Seq.empty, None)
      val interaction = Interaction("interaction", Seq(input), Seq(output))
      val name = "RecipeName"
      val recipe1 = Recipe(name).withInteraction(interaction.withPredefinedIngredients(input.name -> 1))
      val recipe2 = Recipe(name).withInteraction(interaction.withPredefinedIngredients(input.name -> 2))
      RecipeCompiler.compileRecipe(recipe1).recipeId shouldNot be(RecipeCompiler.compileRecipe(recipe2).recipeId)
    }

    "give a list of missing ingredients if an interaction has an ingredient that is not provided by any other event or interaction" in {
      val recipe = Recipe("NonProvidedIngredient")
        .withSensoryEvent(secondEvent)
        .withInteractions(interactionOne)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Ingredient 'initialIngredient' for interaction 'InteractionOne' is not provided by any event or interaction")
    }

    "give an error if the RecipeInstanceId is required and is not of the String type" in {
      val wrongrecipeInstanceIdInteraction =
        Interaction(
          name = "wrongrecipeInstanceIdInteraction",
          inputIngredients = Seq(new Ingredient[Int](common.recipeInstanceIdName), initialIngredient),
          output = Seq.empty)

      val recipe = Recipe("NonProvidedIngredient")
        .withSensoryEvent(initialEvent)
        .withInteractions(wrongrecipeInstanceIdInteraction)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Non supported process id type: Int32 on interaction: 'wrongrecipeInstanceIdInteraction'")
    }

    "give a list of wrong ingredients" when {
      "an ingredient is of the wrong type" in {
        val initialIngredientInt = new common.Ingredient("initialIngredient", RecordType(Seq(RecordField("data", Int32))))
        val initialEventInt = Event("InitialEvent", Seq(initialIngredientInt), None)

        val recipe = Recipe("WrongTypedIngredient")
          .withInteractions(
            interactionOne)
          .withSensoryEvent(initialEventInt)

        val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
        compiledRecipe.validationErrors should contain("Interaction 'InteractionOne' expects ingredient 'initialIngredient:CharArray', however incompatible type: 'Record(data: Int32)' was provided")
      }

      "an optional ingredient is of the wrong Option type" in {
        val initialIngredientOptionalInt = Ingredient[Optional[Int]]("initialIngredientOptionalInt")
        val initialIngredientOptionalString = Ingredient[Optional[String]]("initialIngredientOptionalInt")
        val initialIngredientOptionInt = Ingredient[Option[List[Int]]]("initialIngredientOptionInt")
        val initialIngredientOptionString = Ingredient[Option[List[String]]]("initialIngredientOptionInt")
        val initialEventIntOptional = Event("initialEventIntOptional", Seq(initialIngredientOptionalString), None)
        val initialEventIntOption = Event("initialEventIntOption", Seq(initialIngredientOptionString), None)
        val interactionOptional =
          Interaction(
            name = "InteractionWithOptional",
            inputIngredients = Seq(recipeInstanceId, initialIngredientOptionalInt, initialIngredientOptionInt),
            output = Seq.empty)

        val recipe = Recipe("WrongTypedOptionalIngredient")
          .withInteractions(
            interactionOptional)
          .withSensoryEvents(initialEventIntOptional, initialEventIntOption)

        val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
        compiledRecipe.validationErrors should contain("Interaction 'InteractionWithOptional' expects ingredient 'initialIngredientOptionalInt:Option[Int32]', however incompatible type: 'Option[CharArray]' was provided")
        compiledRecipe.validationErrors should contain("Interaction 'InteractionWithOptional' expects ingredient 'initialIngredientOptionInt:Option[List[Int32]]', however incompatible type: 'Option[List[CharArray]]' was provided")
      }
    }

    "give a validation error for an empty/non-logical recipe" in {
      RecipeCompiler.compileRecipe(Recipe("someName")).validationErrors should contain only(
        "No sensory events found.",
        "No interactions found."
      )
    }

    "give no errors if an Optional ingredient is of the correct Option type" in {
      val initialIngredientInt = Ingredient[Optional[List[Int]]]("initialIngredient")
      val initialEventInt = Event("InitialEvent", Seq(initialIngredientInt), None)
      val interactionOptional =
        Interaction(
          name = "InteractionWithOptional",
          inputIngredients = Seq(recipeInstanceId, initialIngredientInt),
          output = Seq.empty)

      val recipe = Recipe("CorrectTypedOptionalIngredient")
        .withInteractions(
          interactionOptional)
        .withSensoryEvent(initialEventInt)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe empty
    }

    "give a list of wrong ingredients if a predefined ingredient is of the wrong type" in {
      val recipe = Recipe("WrongGivenPredefinedIngredient")
        .withInteractions(
          interactionOne
            .withRequiredEvent(initialEvent)
            .withPredefinedIngredients(("initialIngredient", Integer.valueOf(12))))
        .withSensoryEvent(initialEvent)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Predefined argument 'initialIngredient' is not of type: CharArray on interaction: 'InteractionOne'")
    }

    "give a list of wrong ingredients if a predefined ingredient is not needed by the interaction" in {
      val recipe = Recipe("WrongGivenIngredient")
        .withInteractions(
          interactionOne
            .withPredefinedIngredients(("WrongIngredient", null)))
        .withSensoryEvent(initialEvent)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Predefined argument 'WrongIngredient' is not defined on interaction: 'InteractionOne'")
    }

    "validate if unreachable interactions exist or not" in {
      val recipe = Recipe("RecipeWithUnreachableInteraction")
        .withInteractions(interactionSeven.withMaximumInteractionCount(1), interactionEight)
        .withSensoryEvent(initialEvent)

      val compiledRecipe = RecipeCompiler.compileRecipe(recipe,
        ValidationSettings(allowNonExecutableInteractions = false))

      compiledRecipe.validationErrors should contain("InteractionEight is not executable")
    }

    "fail compilation" when {
      "the interaction name is null or empty" in {
        List("", null) foreach { name =>
          val invalidInteraction = Interaction(name, Seq.empty, Seq())
          val recipe = Recipe("InteractionNameTest").withInteractions(invalidInteraction).withSensoryEvent(initialEvent)

          intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)).getMessage.shouldBe("Interaction with a null or empty name found")
        }
      }


      "the event name is null or empty" in {
        List("", null) foreach { name =>
          val invalidEvent = Event(name)
          val recipe = Recipe("EventNameTest").withSensoryEvent(invalidEvent).withInteraction(interactionOne)

          intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)).getMessage.shouldBe("Event with a null or empty name found")
        }
      }

      "the ingredient name is null or empty" in {
        List("", null) foreach { name =>
          val invalidIngredient = Ingredient[String](name)
          val recipe = Recipe("IngredientNameTest").withSensoryEvent(Event("someEvent", invalidIngredient)).withInteraction(interactionOne)

          intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)).getMessage.shouldBe("Ingredient with a null or empty name found")
        }
      }

      "the recipe name is null or empty" in {
        List("", null) foreach { name =>
          val recipe = Recipe(name)

          intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)).getMessage.shouldBe("Recipe with a null or empty name found")
        }
      }
    }

    "give the interaction an optional ingredient as empty" when {
      "the ingredient is not provided" in {
        val recipe: Recipe = Recipe("MissingOptionalRecipe")
          .withInteraction(interactionWithOptionalIngredients)
          .withSensoryEvent(initialEvent)

        val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
        compiledRecipe.validationErrors shouldBe List.empty
        compiledRecipe.interactionTransitions
          .map(it =>
            if (it.interactionName.equals("OptionalIngredientInteraction")) {
              it.predefinedParameters.size shouldBe 4
              it.predefinedParameters("missingJavaOptional") shouldBe NullValue
              it.predefinedParameters("missingJavaOptional2") shouldBe NullValue
              it.predefinedParameters("missingScalaOption") shouldBe NullValue
              it.predefinedParameters("missingScalaOption2") shouldBe NullValue
            })
      }
    }

    "give the interaction an optional ingredient with value" when {
      "the ingredient is provided" in {
        val optionalProviderEvent = Event("optionalProviderEvent", missingJavaOptional)

        val recipe: Recipe = Recipe("MissingOptionalRecipe")
          .withInteraction(interactionWithOptionalIngredients)
          .withSensoryEvents(initialEvent, optionalProviderEvent)

        val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
        compiledRecipe.validationErrors shouldBe List.empty
        compiledRecipe.interactionTransitions
          .map(it =>
            if (it.interactionName.equals("OptionalIngredientInteraction")) {
              it.predefinedParameters.size shouldBe 3
              it.predefinedParameters("missingJavaOptional2") shouldBe NullValue
              it.predefinedParameters("missingScalaOption") shouldBe NullValue
              it.predefinedParameters("missingScalaOption2") shouldBe NullValue
            })
      }

      "the ingredient is renamed and provided via an event" in {
        val stringOptionIngredient = Ingredient[Option[String]]("stringOptionIngredient")
        val renamedStringOptionIngredient = Ingredient[Option[String]]("renamedStringOptionIngredient")

        val eventWithOptionIngredient = Event("eventWithOptionIngredient", stringOptionIngredient)

        val interactionWithOptionIngredient = Interaction("interactionWithOptionIngredient", Seq(initialIngredient), Seq(eventWithOptionIngredient))

        val secondInteraction = Interaction("secondInteraction", Seq(renamedStringOptionIngredient), Seq())

        val recipe = Recipe("interactionWithEventOutputTransformer")
          .withSensoryEvent(initialEvent)
          .withInteraction(interactionWithOptionIngredient
            .withEventOutputTransformer(eventWithOptionIngredient, "RenamedEventWithOptionIngredient", Map("stringOptionIngredient" -> "renamedStringOptionIngredient")))
          .withInteraction(secondInteraction)

        val compiledRecipe = RecipeCompiler.compileRecipe(recipe)
        compiledRecipe.validationErrors shouldBe empty

        val transition = compiledRecipe.interactionTransitions.find(_.interactionName == "secondInteraction").get
        transition.nonProvidedIngredients.map(_.name) should contain("renamedStringOptionIngredient")
      }

      "the ingredient is predefined" in {
        val ingredientValue: Optional[String] = java.util.Optional.of("value")
        val recipe: Recipe = Recipe("MissingOptionalRecipe")
          .withInteraction(
            interactionWithOptionalIngredients
              .withPredefinedIngredients(("missingJavaOptional", ingredientValue))
          )
          .withSensoryEvents(initialEvent)

        val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
        compiledRecipe.validationErrors shouldBe List.empty
        compiledRecipe.interactionTransitions
          .map(it =>
            if (it.interactionName.equals("OptionalIngredientInteraction")) {
              it.predefinedParameters.size shouldBe 4
              it.predefinedParameters("missingJavaOptional") shouldBe PrimitiveValue("value")
              it.predefinedParameters("missingJavaOptional2") shouldBe NullValue
              it.predefinedParameters("missingScalaOption") shouldBe NullValue
              it.predefinedParameters("missingScalaOption2") shouldBe NullValue
            })
      }

      "the ingredient is provided, but not wrapped in an Option type" in {
        val optionalProviderEvent = Event("optionalProviderEvent", missingJavaOptionalDirectString)

        val recipe: Recipe = Recipe("MissingOptionalRecipe")
          .withInteraction(interactionWithOptionalIngredients)
          .withSensoryEvents(initialEvent, optionalProviderEvent)

        val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
        compiledRecipe.validationErrors shouldBe List.empty
        compiledRecipe.interactionTransitions
          .map(it =>
            if (it.interactionName.equals("OptionalIngredientInteraction")) {
              it.predefinedParameters.size shouldBe 3
              it.predefinedParameters("missingJavaOptional2") shouldBe NullValue
              it.predefinedParameters("missingScalaOption") shouldBe NullValue
              it.predefinedParameters("missingScalaOption2") shouldBe NullValue
            })
      }
    }

    "give the correct id" when {
      "it compiles a java recipe" in {
        val recipe = TestRecipeJava.getRecipe("id-test-recipe")
        val compiledRecipe = RecipeCompiler.compileRecipe(recipe)
        compiledRecipe.recipeId shouldBe "220827c42a75b3f8"
      }
    }


    "give the interaction for checkpoint-events" when {
      "it compiles a java recipe" in {
        val recipe = TestRecipeJava.getRecipe("id-test-recipe")
          .withCheckpointEvent(CheckPointEvent("Success")
            .withRequiredEvent(initialEvent))
        val compiledRecipe = RecipeCompiler.compileRecipe(recipe)
        compiledRecipe.recipeId shouldBe "753bd775b8582b22"
        compiledRecipe.petriNet.transitions.count { case i: InteractionTransition => i.interactionName.contains(s"${checkpointEventInteractionPrefix}Success") case _ => false } shouldBe 1
      }
    }
  }
}
