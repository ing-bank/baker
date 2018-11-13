package com.ing.baker.compiler

import java.util.Optional

import com.ing.baker.il.{CompiledRecipe, ValidationSettings}
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilDeadline
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe, processId}
import com.ing.baker.types.{NullValue, PrimitiveValue}
import org.scalatest.{Matchers, WordSpecLike}

import scala.concurrent.duration._
import scala.language.postfixOps

class RecipeCompilerSpec extends WordSpecLike with Matchers {

  "The RecipeCompiler should" should {

    "not have validation errors for a valid recipe" in {
      val recipe: Recipe = getRecipe("ValidRecipe")
      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe List.empty

      // dumpToFile("TestRecipe.svg", compiledRecipe.getVisualRecipeAsSVG)
    }

    "should add the exhausted retry event to the interaction event output list if defined" in {
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

    "Generate the same id for same recipe" in {

      (1 to 10)
        .map(_ => getRecipe("ValidRecipe"))
        .map(RecipeCompiler.compileRecipe(_).recipeId)
        .foreach(_ shouldBe "1fc5d434d145c3fb")
    }

    "give a List of missing ingredients if an interaction has an ingredient that is not provided by any other event or interaction" in {
      val recipe = Recipe("NonProvidedIngredient")
        .withSensoryEvent(secondEvent)
        .withInteractions(interactionOne)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Ingredient 'initialIngredient' for interaction 'InteractionOne' is not provided by any event or interaction")
    }

    "give an error if the processId is required and is not of the String type" in {
      val wrongProcessIdInteraction =
        Interaction(
          name = "wrongProcessIdInteraction",
          inputIngredients = Seq(new Ingredient[Int](common.processIdName), initialIngredient),
          output = Seq.empty)

      val recipe = Recipe("NonProvidedIngredient")
        .withSensoryEvent(initialEvent)
        .withInteractions(wrongProcessIdInteraction)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Non supported process id type: Int32 on interaction: 'wrongProcessIdInteraction'")
    }

    "give a list of wrong ingredients if an ingredient is of the wrong type" in {
      val initialIngredientInt = Ingredient[Int]("initialIngredient")
      val initialEventInt = Event("InitialEvent", Seq(initialIngredientInt), None)

      val recipe = Recipe("WrongTypedIngredient")
        .withInteractions(
          interactionOne)
        .withSensoryEvent(initialEventInt)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Interaction 'InteractionOne' expects ingredient 'initialIngredient:CharArray', however incompatible type: 'Int32' was provided")
    }

    "give a list of wrong ingredients if an Optional ingredient is of the wrong Optional type" in {
      val initialIngredientOptionalInt = Ingredient[Optional[Int]]("initialIngredientOptionalInt")
      val initialIngredientOptionalString = Ingredient[Optional[String]]("initialIngredientOptionalInt")
      val initialIngredientOptionInt = Ingredient[Option[List[Int]]]("initialIngredientOptionInt")
      val initialIngredientOptionString = Ingredient[Option[List[String]]]("initialIngredientOptionInt")
      val initialEventIntOptional = Event("initialEventIntOptional", Seq(initialIngredientOptionalString), None)
      val initialEventIntOption = Event("initialEventIntOption", Seq(initialIngredientOptionString), None)
      val interactionOptional =
        Interaction(
          name = "InteractionWithOptional",
          inputIngredients = Seq(processId, initialIngredientOptionalInt, initialIngredientOptionInt),
          output = Seq.empty)

      val recipe = Recipe("WrongTypedOptionalIngredient")
        .withInteractions(
          interactionOptional)
        .withSensoryEvents(initialEventIntOptional, initialEventIntOption)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Interaction 'InteractionWithOptional' expects ingredient 'initialIngredientOptionalInt:OptionType(Int32)', however incompatible type: 'OptionType(CharArray)' was provided")
      compiledRecipe.validationErrors should contain("Interaction 'InteractionWithOptional' expects ingredient 'initialIngredientOptionInt:OptionType(ListType(Int32))', however incompatible type: 'OptionType(ListType(CharArray))' was provided")
    }

    "give an validation error for an empty/non-logical recipe" in {
      RecipeCompiler.compileRecipe(Recipe("someName")).validationErrors should contain only(
        "No sensory events found.",
        "No interactions or sieves found."
      )
    }

    "give no errors if an Optional ingredient is of the correct Optional type" in {
      val initialIngredientInt = Ingredient[Optional[List[Int]]]("initialIngredient")
      val initialEventInt = Event("InitialEvent", Seq(initialIngredientInt), None)
      val interactionOptional =
        Interaction(
          name = "InteractionWithOptional",
          inputIngredients = Seq(processId, initialIngredientInt),
          output = Seq.empty)

      val recipe = Recipe("CorrectTypedOptionalIngredient")
        .withInteractions(
          interactionOptional)
        .withSensoryEvent(initialEventInt)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe empty
    }

    "give a list of wrong ingredients if an predefined ingredient is of the wrong type" in {
      val recipe = Recipe("WrongGivenPredefinedIngredient")
        .withInteractions(
          interactionOne
            .withRequiredEvent(initialEvent)
            .withPredefinedIngredients(("initialIngredient", Integer.valueOf(12))))
        .withSensoryEvent(initialEvent)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Predefined argument 'initialIngredient' is not of type: CharArray on interaction: 'InteractionOne'")
    }

    "give a list of wrong ingredients if an predefined ingredient is not needed by the interaction" in {
      val recipe = Recipe("WrongGivenIngredient")
        .withInteractions(
          interactionOne
            .withPredefinedIngredients(("WrongIngredient", null)))
        .withSensoryEvent(initialEvent)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Predefined argument 'WrongIngredient' is not defined on interaction: 'InteractionOne'")
    }

    "validate if there are unreachable interactions exist or not" in {
      val recipe = Recipe("RecipeWithUnreachableInteraction")
        .withInteractions(interactionSeven.withMaximumInteractionCount(1), interactionEight)
        .withSensoryEvent(initialEvent)

      val compiledRecipe = RecipeCompiler.compileRecipe(recipe,
        ValidationSettings(allowNonExecutableInteractions = false))

      compiledRecipe.validationErrors should contain("InteractionEight is not executable")
    }

    "fail compilation for an empty or null named interaction" in {
      List("", null) foreach { name =>
        val invalidInteraction = Interaction(name, Seq.empty, Seq())
        val recipe = Recipe("InteractionNameTest").withInteractions(invalidInteraction).withSensoryEvent(initialEvent)

        intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)) getMessage() shouldBe "Interaction with a null or empty name found"
      }
    }


    "fail compilation for an empty or null named event" in {
      List("", null) foreach { name =>
        val invalidEvent = Event(name)
        val recipe = Recipe("EventNameTest").withSensoryEvent(invalidEvent).withInteraction(interactionOne)

        intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)) getMessage() shouldBe "Event with a null or empty name found"
      }
    }

    "fail compilation for an empty or null named ingredient" in {
      List("", null) foreach { name =>
        val invalidIngredient = Ingredient[String](name)
        val recipe = Recipe("IngredientNameTest").withSensoryEvent(Event("someEvent", invalidIngredient)).withInteraction(interactionOne)

        intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)) getMessage() shouldBe "Ingredient with a null or empty name found"
      }
    }

    "fail compilation for an empty or null named recipe" in {
      List("", null) foreach { name =>
        val recipe = Recipe(name)

        intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)) getMessage() shouldBe "Recipe with a null or empty name found"
      }
    }

    "interactions with optional ingredients that are NOT provided SHOULD be provided as empty" in {
      val recipe: Recipe = Recipe("MissingOptionalRecipe")
        .withInteraction(optionalIngredientInteraction)
        .withSensoryEvent(initialEvent)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe List.empty
      compiledRecipe.interactionTransitions
        .map(it =>
          if (it.interactionName.equals("OptionalIngredientInteraction")) {
            it.predefinedParameters.size shouldBe 4
            it.predefinedParameters("missingJavaOptional") shouldBe NullValue
            it.predefinedParameters("missingJavaOptional2") shouldBe NullValue
            it.predefinedParameters("missingScalaOptional") shouldBe NullValue
            it.predefinedParameters("missingScalaOptional2") shouldBe NullValue
          })
    }

    "interactions with optional ingredients that ARE provided SHOULD NOT be provided as empty" in {
      val optionalProviderEvent = Event("optionalProviderEvent", missingJavaOptional)

      val recipe: Recipe = Recipe("MissingOptionalRecipe")
        .withInteraction(optionalIngredientInteraction)
        .withSensoryEvents(initialEvent, optionalProviderEvent)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe List.empty
      compiledRecipe.interactionTransitions
        .map(it =>
          if (it.interactionName.equals("OptionalIngredientInteraction")) {
            it.predefinedParameters.size shouldBe 3
            it.predefinedParameters("missingJavaOptional2") shouldBe NullValue
            it.predefinedParameters("missingScalaOptional") shouldBe NullValue
            it.predefinedParameters("missingScalaOptional2") shouldBe NullValue
          })

    }

    "interactions with RENAMED optional ingredients via events that ARE provided SHOULD NOT be provided as empty" in {
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
//      println(compiledRecipe.getRecipeVisualization)
      compiledRecipe.validationErrors shouldBe empty

      val transition = compiledRecipe.interactionTransitions.find(_.interactionName == "secondInteraction").get
      transition.nonProvidedIngredients.map(_.name) should contain("renamedStringOptionIngredient")
    }

    "interactions with ingredients that are provided but are required as Optionals should be wrapped into the optional" in {
      val optionalProviderEvent = Event("optionalProviderEvent", missingJavaOptionalDirectString)

      val recipe: Recipe = Recipe("MissingOptionalRecipe")
        .withInteraction(optionalIngredientInteraction)
        .withSensoryEvents(initialEvent, optionalProviderEvent)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe List.empty
      compiledRecipe.interactionTransitions
        .map(it =>
          if (it.interactionName.equals("OptionalIngredientInteraction")) {
            it.predefinedParameters.size shouldBe 3
            it.predefinedParameters("missingJavaOptional2") shouldBe NullValue
            it.predefinedParameters("missingScalaOptional") shouldBe NullValue
            it.predefinedParameters("missingScalaOptional2") shouldBe NullValue
          })
    }

    "interactions with optional ingredients that are predefined SHOULD NOT be provided as empty" in {
      val ingredientValue: Optional[String] = java.util.Optional.of("value")
      val recipe: Recipe = Recipe("MissingOptionalRecipe")
        .withInteraction(
          optionalIngredientInteraction
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
            it.predefinedParameters("missingScalaOptional") shouldBe NullValue
            it.predefinedParameters("missingScalaOptional2") shouldBe NullValue
          })
    }
  }
}

@deprecated("marked deprecated because of -XFatal-Warnings and deprecated sieves", "1.4.0")
class DepcratedCompilerSpec extends WordSpecLike with Matchers {

  "(deprecated) The RecipeCompiler" should {

    "(deprecated) fail compilation for an empty or null named sieve interaction " in {
      List("", null) foreach { name =>
        val invalidSieveInteraction = Interaction(name, Seq.empty, Seq())
        val recipe = Recipe("SieveNameTest").withSieve(invalidSieveInteraction).withSensoryEvent(initialEvent)

        intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)) getMessage() shouldBe "Sieve Interaction with a null or empty name found"
      }
    }
  }
}
