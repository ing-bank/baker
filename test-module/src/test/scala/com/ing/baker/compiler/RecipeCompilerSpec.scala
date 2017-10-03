package com.ing.baker.compiler

import java.lang.reflect.Type
import java.util.Optional

import com.ing.baker.TestRecipeHelper._
import com.ing.baker._
import com.ing.baker.il.{CompiledRecipe, ValidationSettings}
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.{FiresOneOfEvents, ProvidesIngredient, ProvidesNothing}
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Ingredients, Interaction, Recipe, processId}

import scala.concurrent.duration._
import scala.language.postfixOps

class RecipeCompilerSpec extends TestRecipeHelper {

  override def actorSystemName = "RecipeCompilerSpec"

  before {
    resetMocks
  }

  "The RecipeCompiler should" should {

    "not have validation errors for a valid recipe" in {
      val recipe: Recipe = getComplexRecipe("ValidRecipe")
      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe List.empty
    }

    "should add the exhausted retry event to the interaction event output list if defined" in {
      val exhaustedEvent = Event("RetryExhausted")
      val recipe = Recipe("RetryExhaustedRecipe")
        .withSensoryEvent(initialEvent)
        .withInteractions(interactionOne.withIncrementalBackoffOnFailure(
          initialDelay = 10 milliseconds,
          exhaustedRetryEvent = Some(exhaustedEvent)))

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)

      compiledRecipe.allEvents.map(_.name) should contain(exhaustedEvent.name)
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
        Interaction("wrongProcessIdInteraction",
          Ingredients(new Ingredient[Int](common.ProcessIdName), initialIngredient),
          ProvidesIngredient(interactionOneOriginalIngredient))

      val recipe = Recipe("NonProvidedIngredient")
        .withSensoryEvent(initialEvent)
        .withInteractions(wrongProcessIdInteraction)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Non supported process id type: int on interaction: 'wrongProcessIdInteraction'")
    }

    "give a list of wrong ingredients if an ingredient is of the wrong type" in {
      val initialIngredientInt = Ingredient[Int]("initialIngredient")
      val initialEventInt = Event("InitialEvent", initialIngredientInt, None)

      val recipe = Recipe("WrongTypedIngredient")
        .withInteractions(
          interactionOne)
        .withSensoryEvent(initialEventInt)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Interaction 'InteractionOne' expects ingredient 'initialIngredient:class java.lang.String', however incompatible type: 'int' was provided")
    }

    "give a list of wrong ingredients if an Optional ingredient is of the wrong Optional type" in {
      val initialIngredientOptionalInt = Ingredient[Optional[Int]]("initialIngredientOptionalInt")
      val initialIngredientOptionalString = Ingredient[Optional[String]]("initialIngredientOptionalInt")
      val initialIngredientOptionInt = Ingredient[Option[List[Int]]]("initialIngredientOptionInt")
      val initialIngredientOptionString = Ingredient[Option[List[String]]]("initialIngredientOptionInt")
      val initialEventIntOptional = Event("initialEventIntOptional", initialIngredientOptionalString, None)
      val initialEventIntOption = Event("initialEventIntOption", initialIngredientOptionString, None)
      val interactionOptional =
        Interaction("InteractionWithOptional",
          Ingredients(processId, initialIngredientOptionalInt, initialIngredientOptionInt),
          ProvidesNothing)

      val recipe = Recipe("WrongTypedOptionalIngredient")
        .withInteractions(
          interactionOptional)
        .withSensoryEvents(initialEventIntOptional, initialEventIntOption)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors should contain("Interaction 'InteractionWithOptional' expects ingredient 'initialIngredientOptionalInt:ParameterizedType: class java.util.Optional[int]', however incompatible type: 'ParameterizedType: class java.util.Optional[class java.lang.String]' was provided")
      compiledRecipe.validationErrors should contain("Interaction 'InteractionWithOptional' expects ingredient 'initialIngredientOptionInt:ParameterizedType: class scala.Option[ParameterizedType: class scala.collection.immutable.List[int]]', however incompatible type: 'ParameterizedType: class scala.Option[ParameterizedType: class scala.collection.immutable.List[class java.lang.String]]' was provided")
    }

    "give an validation error for an empty/non-logical recipe" in {
      RecipeCompiler.compileRecipe(Recipe("someName")).validationErrors should contain only(
        "No sensory events found.",
        "No interactions or sieves found."
      )
    }

    "give no errors if an Optional ingredient is of the correct Optional type" in {
      val initialIngredientInt = Ingredient[Optional[List[Int]]]("initialIngredient")
      val initialEventInt = Event("InitialEvent", initialIngredientInt, None)
      val interactionOptional =
        Interaction("InteractionWithOptional",
          Ingredients(processId, initialIngredientInt),
          ProvidesNothing)

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
      compiledRecipe.validationErrors should contain("Predefined argument 'initialIngredient' is not of type: class java.lang.String on interaction: 'InteractionOne'")
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

    "validate that ingredients are not of primitive types" in {

      val primitiveIntIngredient = new common.Ingredient {
        override val name: String = "age"
        override val clazz: Type = Integer.TYPE
      }

      val interactionRequiringPrimitive = Interaction("DoSomething", Seq(primitiveIntIngredient), ProvidesNothing)

      val eventProvidingPrimitive = Event("FooEvent", primitiveIntIngredient)

      val recipe = Recipe("RecipeWithPrimitiveTypedIngredients")
          .withInteraction(interactionRequiringPrimitive)
            .withSensoryEvent(eventProvidingPrimitive)

      // there is only one ingredient, enought to check
      RecipeCompiler.compileRecipe(recipe).validationErrors should contain ("Ingredient 'age' is of primitive type 'int', primitive types are not supported for ingredients")
    }

    "fail compilation for an empty or null named interaction" in {
      List("", null) foreach { name =>
        val invalidInteraction = Interaction(name, Seq.empty, ProvidesNothing)
        val recipe = Recipe("InteractionNameTest").withInteractions(invalidInteraction).withSensoryEvent(initialEvent)

        intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)) getMessage() shouldBe "Interaction with a null or empty name found"
      }
    }

    "fail compilation for an empty or null named sieve interaction" in {
      List("", null) foreach { name =>
        val invalidSieveInteraction = Interaction(name, Seq.empty, ProvidesNothing)
        val recipe = Recipe("SieveNameTest").withSieve(invalidSieveInteraction).withSensoryEvent(initialEvent)

        intercept[IllegalArgumentException](RecipeCompiler.compileRecipe(recipe)) getMessage() shouldBe "Sieve Interaction with a null or empty name found"
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

    "interactions with optional ingredients that are NOT provided should be provided as empty" in {
      val recipe: Recipe = Recipe("MissingOptionalRecipe")
        .withInteraction(optionalIngredientInteraction)
        .withSensoryEvent(initialEvent)

      val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(recipe)
      compiledRecipe.validationErrors shouldBe List.empty
      compiledRecipe.interactionTransitions
        .map(it =>
          if (it.interactionName.equals("OptionalIngredientInteraction")) {
            it.predefinedParameters.size shouldBe 4
            it.predefinedParameters("missingJavaOptional") shouldBe Optional.empty()
            it.predefinedParameters("missingJavaOptional2") shouldBe Optional.empty()
            it.predefinedParameters("missingScalaOptional") shouldBe Option.empty
            it.predefinedParameters("missingScalaOptional2") shouldBe Option.empty
          })
    }

    "interactions with optional ingredients that are provided should NOT be provided as empty" in {
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
            it.predefinedParameters("missingJavaOptional2") shouldBe Optional.empty()
            it.predefinedParameters("missingScalaOptional") shouldBe Option.empty
            it.predefinedParameters("missingScalaOptional2") shouldBe Option.empty
          })

    }

    "interactions with RENAMED optional ingredients via events that are provided should NOT be provided as empty" in {
      val stringOptionIngredient = Ingredient[Option[String]]("stringOptionIngredient")
      val renamedStringOptionIngredient = Ingredient[Option[String]]("renamedStringOptionIngredient")

      val eventWithOptionIngredient = Event("eventWithOptionIngredient", stringOptionIngredient)

      val interactionWithOptionIngredient = Interaction("interactionWithOptionIngredient", Seq(initialIngredient), FiresOneOfEvents(eventWithOptionIngredient))
      val secondInteraction = Interaction("secondInteraction", Seq(renamedStringOptionIngredient), ProvidesIngredient(Ingredient[String]("someIngredient")))

      val recipe = Recipe("interactionWithEventOutputTransformer")
        .withSensoryEvent(initialEvent)
        .withInteraction(interactionWithOptionIngredient
          .withEventOutputTransformer(eventWithOptionIngredient, "RenamedEventWithOptionIngredient", Map("stringOptionIngredient" -> "renamedStringOptionIngredient")))
        .withInteraction(secondInteraction)

      val compiledRecipe = RecipeCompiler.compileRecipe(recipe)
      println(compiledRecipe.getRecipeVisualization)
      compiledRecipe.validationErrors shouldBe empty

      val transition = compiledRecipe.interactionTransitions.find(_.interactionName == "secondInteraction").get
      transition.nonProvidedIngredients.keys should contain("renamedStringOptionIngredient")
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
            it.predefinedParameters("missingJavaOptional2") shouldBe Optional.empty()
            it.predefinedParameters("missingScalaOptional") shouldBe Option.empty
            it.predefinedParameters("missingScalaOptional2") shouldBe Option.empty
          })
    }

    "interactions with optional ingredients that are predefined should not be provided as empty" in {
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
            it.predefinedParameters("missingJavaOptional") shouldBe ingredientValue
            it.predefinedParameters("missingJavaOptional2") shouldBe Optional.empty()
            it.predefinedParameters("missingScalaOptional") shouldBe Option.empty
            it.predefinedParameters("missingScalaOptional2") shouldBe Option.empty
          })
    }

  }
}
