package com.ing.baker.compiler

import com.ing.baker.compiler.ScalaConversions.asJava
import com.ing.baker.compiler.ScalaConversions.asScala
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.EventDescriptor
import com.ing.baker.il.IngredientDescriptor
import com.ing.baker.il.ValidationSettings
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.recipe.TestRecipe.eventFromInteractionTwo
import com.ing.baker.recipe.TestRecipe.exhaustedEvent
import com.ing.baker.recipe.TestRecipe.getRecipe
import com.ing.baker.recipe.TestRecipe.initialEvent
import com.ing.baker.recipe.TestRecipe.initialEventExtendedName
import com.ing.baker.recipe.TestRecipe.initialIngredient
import com.ing.baker.recipe.TestRecipe.interactionEight
import com.ing.baker.recipe.TestRecipe.interactionFive
import com.ing.baker.recipe.TestRecipe.interactionFour
import com.ing.baker.recipe.TestRecipe.interactionOne
import com.ing.baker.recipe.TestRecipe.interactionOneSuccessful
import com.ing.baker.recipe.TestRecipe.interactionSeven
import com.ing.baker.recipe.TestRecipe.interactionSix
import com.ing.baker.recipe.TestRecipe.interactionThree
import com.ing.baker.recipe.TestRecipe.interactionTwo
import com.ing.baker.recipe.TestRecipe.interactionWithOptionalIngredients
import com.ing.baker.recipe.TestRecipe.missingJavaOptional
import com.ing.baker.recipe.TestRecipe.missingJavaOptionalDirectString
import com.ing.baker.recipe.TestRecipe.notUsedSensoryEvent
import com.ing.baker.recipe.TestRecipe.providesNothingInteraction
import com.ing.baker.recipe.TestRecipe.secondEvent
import com.ing.baker.recipe.TestRecipe.sieveInteraction
import com.ing.baker.recipe.TestRecipeJava
import com.ing.baker.recipe.common.EventOutputTransformer
import com.ing.baker.recipe.common.Ingredient
import com.ing.baker.recipe.common.InteractionDescriptor
import com.ing.baker.recipe.common.`package$`
import com.ing.baker.recipe.scaladsl.CheckPointEvent
import com.ing.baker.recipe.scaladsl.Event
import com.ing.baker.recipe.scaladsl.Interaction
import com.ing.baker.recipe.scaladsl.`Interaction$`
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.types.Converters
import com.ing.baker.types.`Int32$`
import com.ing.baker.types.`NullValue$`
import com.ing.baker.types.PrimitiveValue
import com.ing.baker.types.RecordField
import com.ing.baker.types.RecordType
import com.ing.baker.types.Value
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.fail
import scala.Option
import scala.Some
import scala.Tuple2
import scala.collection.immutable.Seq
import scala.concurrent.duration.Duration
import java.util.Optional
import java.util.concurrent.TimeUnit
import kotlin.reflect.javaType
import kotlin.reflect.typeOf

class RecipeCompilerScalaTest {

    @Test
    fun `The recipe compiler should not have validation errors for a valid recipe`() {
        val recipe: Recipe = getRecipe("ValidRecipe")
        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue(compiledRecipe.validationErrors.isEmpty())
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined with FireEventAfterFailure (with name)`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAfterFailure(Some(exhaustedEvent().name()))
                )
            )
        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue(exhaustedEvent().name() in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined with FireEventAfterFailure (no name)`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAfterFailure(Option.empty())
                )
            )
        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue("InteractionOneRetryExhausted" in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined with FireEventAndBlock (with name)`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAndBlock(Some(exhaustedEvent().name()))
                )
            )
        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue(exhaustedEvent().name() in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined with FireEventAndBlock (no name)`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAndBlock(Option.empty())
                )
            )
        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue("InteractionOneRetryExhausted" in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined with FireEventAndResolve (with name)`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAndResolve(Some(exhaustedEvent().name()))
                )
            )
        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue(exhaustedEvent().name() in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined with FireEventAndResolve (no name)`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAndResolve(Option.empty())
                )
            )
        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue("InteractionOneFunctionalFailed" in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined  with withFireRetryExhaustedEvent`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
                        .withInitialDelay(10.milliseconds)
                        .withUntil(Some(UntilDeadline(10.seconds)))
                        .withFireRetryExhaustedEvent(exhaustedEvent())
                        .build()
                )
            )

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        assertTrue(exhaustedEvent().name() in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined  with withFireRetryExhaustedEvent 2`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
                        .withInitialDelay(10.milliseconds)
                        .withUntil(Some(UntilDeadline(10.seconds)))
                        .withFireRetryExhaustedEvent(Some("RetryExhausted"))
                        .build()
                )
            )

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        assertTrue(exhaustedEvent().name() in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined  with withFireRetryExhaustedEvent 3`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
                        .withInitialDelay(10.milliseconds)
                        .withUntil(Some(UntilDeadline(10.seconds)))
                        .withFireRetryExhaustedEvent()
                        .build()
                )
            )

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        assertTrue("InteractionOneRetryExhausted" in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined with withFireEventAndBlock`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
                        .withInitialDelay(10.milliseconds)
                        .withUntil(Some(UntilDeadline(10.seconds)))
                        .withFireRetryExhaustedEvent(exhaustedEvent())
                        .build()
                )
            )

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        assertTrue(exhaustedEvent().name() in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined with withFireEventAndBlock 2`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
                        .withInitialDelay(10.milliseconds)
                        .withUntil(Some(UntilDeadline(10.seconds)))
                        .withFireRetryExhaustedEvent(Some("RetryExhausted"))
                        .build()
                )
            )

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        assertTrue(exhaustedEvent().name() in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined with withFireEventAndBlock 3`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
                        .withInitialDelay(10.milliseconds)
                        .withUntil(Some(UntilDeadline(10.seconds)))
                        .withFireEventAndBlock()
                        .build()
                )
            )

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        assertTrue("InteractionOneRetryExhausted" in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined with withFireEventAndResolve`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
                        .withInitialDelay(10.milliseconds)
                        .withUntil(Some(UntilDeadline(10.seconds)))
                        .withFireEventAndResolve(exhaustedEvent())
                        .build()
                )
            )

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        assertTrue(exhaustedEvent().name() in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined with withFireEventAndResolve 2`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
                        .withInitialDelay(10.milliseconds)
                        .withUntil(Some(UntilDeadline(10.seconds)))
                        .withFireEventAndResolve(Some("RetryExhausted"))
                        .build()
                )
            )

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        assertTrue(exhaustedEvent().name() in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should add the exhausted retry event to the interaction event output list if defined with withFireEventAndResolve32`() {
        val recipe = recipe("RetryExhaustedRecipe")
            .withSensoryEvent(initialEvent())
            .withInteractions(
                interactionOne().withFailureStrategy(
                    InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
                        .withInitialDelay(10.milliseconds)
                        .withUntil(Some(UntilDeadline(10.seconds)))
                        .withFireEventAndResolve()
                        .build()
                )
            )

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        assertTrue("InteractionOneFunctionalFailed" in compiledRecipe.allEvents.map(EventDescriptor::name))
    }

    @Test
    fun `The recipe compiler should generate the same id for the same recipe`() {
        val first = RecipeCompiler.compileRecipe(getRecipe("ValidRecipe")).recipeId()
        (1..10)
            .map { getRecipe("ValidRecipe") }
            .map { RecipeCompiler.compileRecipe(it).recipeId() }
            .forEach { assertEquals(first, it) }
    }

    @Test
    fun `The recipe compiler should generate different ids for recipes with changes on transitions other than the name`() {
        val input = ingredient<Int>("ingredient")
        val output = event("event", emptyList())
        val interaction = interaction("interaction", listOf(input), listOf(output))
        val name = "RecipeName"
        val recipe1 = recipe(name).withInteraction(interaction.withPredefinedIngredients(input.name() to 1))
        val recipe2 = recipe(name).withInteraction(interaction.withPredefinedIngredients(input.name() to 2))
        assertTrue(RecipeCompiler.compileRecipe(recipe1).recipeId() != RecipeCompiler.compileRecipe(recipe2).recipeId())
    }

    @Test
    fun `The recipe compiler should give a list of missing ingredients if an interaction has an ingredient that is not provided by any other event or interaction`() {
        val recipe = recipe("NonProvidedIngredient")
            .withSensoryEvent(secondEvent())
            .withInteractions(interactionOne())

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue("Ingredient 'initialIngredient' for interaction 'InteractionOne' is not provided by any event or interaction" in compiledRecipe.validationErrors)
    }

    @Test
    fun `The recipe compiler should give an error if the RecipeInstanceId is required and is not of the String type`() {
        val wrongrecipeInstanceIdInteraction =
            interaction(
                name = "wrongrecipeInstanceIdInteraction",
                inputIngredients = listOf(ingredient<Int>(common.recipeInstanceIdName), initialIngredient()),
                output = emptyList()
            )

        val recipe = recipe("NonProvidedIngredient")
            .withSensoryEvent(initialEvent())
            .withInteractions(wrongrecipeInstanceIdInteraction)

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue("Non supported process id type: Int32 on interaction: 'wrongrecipeInstanceIdInteraction'" in compiledRecipe.validationErrors)
    }

    @Test
    fun `The recipe compiler should give an error if the MetaData is required and is not of the Map String to String type`() {
        val wrongMetaDataInteraction =
            interaction(
                name = "wrongMetaDataInteraction",
                inputIngredients = listOf(ingredient<Int>(common.recipeInstanceMetadataName), initialIngredient()),
                output = emptyList()
            )

        val recipe = recipe("NonProvidedIngredient")
            .withSensoryEvent(initialEvent())
            .withInteractions(wrongMetaDataInteraction)

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue("Non supported MetaData type: Int32 on interaction: 'wrongMetaDataInteraction'" in compiledRecipe.validationErrors)
    }

    @Test
    fun `The recipe compiler should give an error if the baker internal ingredients are provided`() {
        val wrongDateEvent = event(
            "WrongDataEvent",
            listOf(
                ingredient<String>("recipeInstanceId"),
                ingredient<String>("RecipeInstanceMetaData")
            ),
            maxFiringLimit = null
        )

        val wrongDateEvent2 = event(
            "WrongDataEvent2",
            listOf(ingredient<String>("RecipeInstanceEventList")),
            maxFiringLimit = null
        )

        val wrongMetaDataInteraction =
            interaction(
                name = "wrongDataProvidedInteraction",
                inputIngredients = listOf(ingredient<String>(common.recipeInstanceIdName), initialIngredient()),
                output = listOf(wrongDateEvent2)
            )

        val recipe = recipe("WrongDataRecipe")
            .withSensoryEvents(initialEvent(), wrongDateEvent)
            .withInteractions(wrongMetaDataInteraction)

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertEquals(
            listOf(
                "Ingredient 'RecipeInstanceMetaData' is provided and this is a reserved name for internal use in Baker",
                "Ingredient 'recipeInstanceId' is provided and this is a reserved name for internal use in Baker",
                "Ingredient 'RecipeInstanceEventList' is provided and this is a reserved name for internal use in Baker"
            ).sorted(),
            compiledRecipe.validationErrors.sorted()
        )
    }

    @Test
    fun `The recipe compiler should give a list of wrong ingredients when an ingredient is of the wrong type`() {
        val initialIngredientInt = Ingredient(
            "initialIngredient", recordType(
                listOf(
                    RecordField("data", Int32)
                )
            )
        )
        val initialEventInt = event("InitialEvent", listOf(initialIngredientInt))

        val recipe = recipe("WrongTypedIngredient")
            .withInteractions(
                interactionOne()
            )
            .withSensoryEvent(initialEventInt)

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue("Interaction 'InteractionOne' expects ingredient 'initialIngredient:CharArray', however incompatible type: 'Record(data: Int32)' was provided" in compiledRecipe.validationErrors)
    }

    @Test
    fun `The recipe compiler should give a list of wrong ingredients when an optional ingredient is of the wrong Option type`() {
        val initialIngredientOptionalInt = ingredient<Optional<Int>>("initialIngredientOptionalInt")
        val initialIngredientOptionalString = ingredient<Optional<String>>("initialIngredientOptionalInt")
        val initialIngredientOptionInt = ingredient<Option<List<Int>>>("initialIngredientOptionInt")
        val initialIngredientOptionString = ingredient<Option<List<String>>>("initialIngredientOptionInt")
        val initialEventIntOptional = event("initialEventIntOptional", listOf(initialIngredientOptionalString))
        val initialEventIntOption = event("initialEventIntOption", listOf(initialIngredientOptionString))
        val interactionOptional =
            interaction(
                name = "InteractionWithOptional",
                inputIngredients = listOf(recipeInstanceId, initialIngredientOptionalInt, initialIngredientOptionInt),
                output = emptyList()
            )

        val recipe = recipe("WrongTypedOptionalIngredient")
            .withInteractions(
                interactionOptional
            )
            .withSensoryEvents(initialEventIntOptional, initialEventIntOption)

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue("Interaction 'InteractionWithOptional' expects ingredient 'initialIngredientOptionalInt:Option[Int32]', however incompatible type: 'Option[CharArray]' was provided" in compiledRecipe.validationErrors)
        assertTrue("Interaction 'InteractionWithOptional' expects ingredient 'initialIngredientOptionInt:Option[List[Int32]]', however incompatible type: 'Option[List[CharArray]]' was provided" in compiledRecipe.validationErrors)
    }

    @Test
    fun `The recipe compiler should give no errors if an Optional ingredient is of the correct Option type`() {
        val initialIngredientInt = ingredient<Optional<List<Int>>>("initialIngredient")
        val initialEventInt = event("InitialEvent", listOf(initialIngredientInt))
        val interactionOptional =
            interaction(
                name = "InteractionWithOptional",
                inputIngredients = listOf(recipeInstanceId, initialIngredientInt),
                output = emptyList()
            )

        val recipe = recipe("CorrectTypedOptionalIngredient")
            .withInteractions(
                interactionOptional
            )
            .withSensoryEvent(initialEventInt)

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue(compiledRecipe.validationErrors.isEmpty())
    }

    @Test
    fun `The recipe compiler should give a list of wrong ingredients if a predefined ingredient is of the wrong type`() {
        val recipe = recipe("WrongGivenPredefinedIngredient")
            .withInteractions(
                interactionOne()
                    .withRequiredEvent(initialEvent())
                    .withPredefinedIngredients("initialIngredient" to Integer.valueOf(12))
            )
            .withSensoryEvent(initialEvent())

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue("Predefined argument 'initialIngredient' is not of type: CharArray on interaction: 'InteractionOne'" in compiledRecipe.validationErrors)
    }

    @Test
    fun `The recipe compiler should give a list of wrong ingredients if a predefined ingredient is not needed by the interaction`() {
        val recipe = recipe("WrongGivenIngredient")
            .withInteractions(
                interactionOne()
                    .withPredefinedIngredients("WrongIngredient" to null)
            )
            .withSensoryEvent(initialEvent())

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue("Predefined argument 'WrongIngredient' is not defined on interaction: 'InteractionOne'" in compiledRecipe.validationErrors)
    }

    @Test
    fun `The recipe compiler should validate if unreachable interactions exist or not`() {
        val recipe = recipe("RecipeWithUnreachableInteraction")
            .withInteractions(interactionSeven().withMaximumInteractionCount(1), interactionEight())
            .withSensoryEvent(initialEvent())

        val compiledRecipe = RecipeCompiler.compileRecipe(
            recipe,
            ValidationSettings(true, true , false)
        )

        assertTrue("InteractionEight is not executable" in compiledRecipe.validationErrors)
    }

    @Test
    fun `The recipe compiler should fail compilation when the interaction name is null or empty`() {
        listOf("", null).forEach { name ->
            val invalidInteraction = interaction(name, emptyList(), emptyList())
            val recipe =
                recipe("InteractionNameTest").withInteractions(invalidInteraction).withSensoryEvent(initialEvent())

            assertFailsWith<RecipeValidationException>(exceptionMessage = "Interaction with a null or empty name found") {
                RecipeCompilerKotlin.compileRecipe(recipe)
            }
        }
    }

    @Test
    fun `The recipe compiler should fail compilation when the event name is null or empty`() {
        listOf("", null).forEach { name ->
            val invalidEvent = event(name)
            val recipe = recipe("EventNameTest").withSensoryEvent(invalidEvent).withInteraction(interactionOne())

            assertFailsWith<RecipeValidationException>(exceptionMessage = "Event with a null or empty name found") {
                RecipeCompilerKotlin.compileRecipe(recipe)
            }
        }
    }

    @Test
    fun `The recipe compiler should fail compilation when the ingredient name is null or empty`() {
        listOf("", null).forEach { name ->
            val invalidIngredient = ingredient<String>(name)
            val recipe = recipe("IngredientNameTest").withSensoryEvent(event("someEvent", listOf(invalidIngredient)))
                .withInteraction(interactionOne())

            assertFailsWith<RecipeValidationException>(exceptionMessage = "Ingredient with a null or empty name found") {
                RecipeCompilerKotlin.compileRecipe(recipe)
            }
        }
    }

    @Test
    fun `The recipe compiler should fail compilation when the recipe name is null or empty`() {
        listOf("", null).forEach { name ->
            val recipe = recipe(name)

            assertFailsWith<RecipeValidationException>(exceptionMessage = "Recipe with a null or empty name found") {
                RecipeCompilerKotlin.compileRecipe(recipe)
            }
        }
    }

    @Test
    fun `The recipe compiler should report an error when an Interaction is reprovider, but has no required events`() {
        val recipe: Recipe = recipe("LoopingWithReprovider")
            .withInteraction(interactionOne().isReprovider(true))
            .withSensoryEvents(initialEvent())

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertEquals(
            listOf("Reprovider interaction InteractionOne needs to have a event precondition"),
            compiledRecipe.validationErrors
        )
    }

    @Test
    fun `The recipe compiler should give the interaction an optional ingredient as empty when the ingredient is not provided`() {
        val recipe: Recipe = recipe("MissingOptionalRecipe")
            .withInteraction(interactionWithOptionalIngredients())
            .withSensoryEvent(initialEvent())

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        assertTrue(compiledRecipe.validationErrors.isEmpty())
        compiledRecipe.interactionTransitions().foreach { transition ->
            if (transition.interactionName().equals("OptionalIngredientInteraction")) {
                assertEquals(4, transition.predefinedParameters().size())
                assertEquals(Some(NullValue), transition.predefinedParameters()["missingJavaOptional"])
                assertEquals(Some(NullValue), transition.predefinedParameters()["missingJavaOptional2"])
                assertEquals(Some(NullValue), transition.predefinedParameters()["missingScalaOption"])
                assertEquals(Some(NullValue), transition.predefinedParameters()["missingScalaOption2"])
            }
        }
    }

    @Test
    fun `The recipe compiler should give the interaction an optional ingredient with value when the ingredient is provided`() {
        val optionalProviderEvent = event("optionalProviderEvent", listOf(missingJavaOptional()))

        val recipe: Recipe = recipe("MissingOptionalRecipe")
            .withInteraction(interactionWithOptionalIngredients())
            .withSensoryEvents(initialEvent(), optionalProviderEvent)

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        assertTrue(compiledRecipe.validationErrors.isEmpty())
        compiledRecipe.interactionTransitions().foreach { transition ->
            if (transition.interactionName().equals("OptionalIngredientInteraction")) {
                assertEquals(3, transition.predefinedParameters().size())
                assertEquals(Some(NullValue), transition.predefinedParameters()["missingJavaOptional2"])
                assertEquals(Some(NullValue), transition.predefinedParameters()["missingScalaOption"])
                assertEquals(Some(NullValue), transition.predefinedParameters()["missingScalaOption2"])
            }
        }
    }

    @Test
    fun `The recipe compiler should give the interaction an optional ingredient with value when the ingredient is renamed and provided via an event`() {
        val stringOptionIngredient = ingredient<Option<String>>("stringOptionIngredient")
        val renamedStringOptionIngredient = ingredient<Option<String>>("renamedStringOptionIngredient")

        val eventWithOptionIngredient = event("eventWithOptionIngredient", listOf(stringOptionIngredient))

        val interactionWithOptionIngredient =
            interaction("interactionWithOptionIngredient", listOf(initialIngredient()), listOf(eventWithOptionIngredient))

        val secondInteraction = interaction("secondInteraction", listOf(renamedStringOptionIngredient), emptyList())

        val recipe = recipe("interactionWithEventOutputTransformer")
            .withSensoryEvent(initialEvent())
            .withInteraction(
                interactionWithOptionIngredient
                    .withEventOutputTransformer(
                        eventWithOptionIngredient,
                        "RenamedEventWithOptionIngredient",
                        mapOf("stringOptionIngredient" to "renamedStringOptionIngredient").asScala
                    )
            )
            .withInteraction(secondInteraction)

        val compiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertTrue(compiledRecipe.validationErrors.isEmpty())

        val transition =
            compiledRecipe.interactionTransitions().find { it.interactionName() == "secondInteraction" }.get()
        assertTrue(
            "renamedStringOptionIngredient" in transition.nonProvidedIngredients().asJava.map(
                IngredientDescriptor::name
            )
        )
    }

    @Test
    fun `The recipe compiler should give the interaction an optional ingredient with value when the ingredient is predefined`() {
        val ingredientValue = Optional.of("value")
        val recipe: Recipe = recipe("MissingOptionalRecipe")
            .withInteraction(
                interactionWithOptionalIngredients()
                    .withPredefinedIngredients("missingJavaOptional" to ingredientValue)
            )
            .withSensoryEvents(initialEvent())

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        assertTrue(compiledRecipe.validationErrors.isEmpty())
        compiledRecipe.interactionTransitions().foreach { transition ->
            if (transition.interactionName().equals("OptionalIngredientInteraction")) {
                assertEquals(4, transition.predefinedParameters().size())
                assertEquals(Some(PrimitiveValue("value")), transition.predefinedParameters()["missingJavaOptional"])
                assertEquals(Some(NullValue), transition.predefinedParameters()["missingJavaOptional2"])
                assertEquals(Some(NullValue), transition.predefinedParameters()["missingScalaOption"])
                assertEquals(Some(NullValue), transition.predefinedParameters()["missingScalaOption2"])
            }
        }
    }

    @Test
    fun `The recipe compiler should give the interaction an optional ingredient with value when the ingredient is provided, but not wrapped in an Option type`() {
        val optionalProviderEvent = event("optionalProviderEvent", listOf(missingJavaOptionalDirectString()))

        val recipe: Recipe = recipe("MissingOptionalRecipe")
            .withInteraction(interactionWithOptionalIngredients())
            .withSensoryEvents(initialEvent(), optionalProviderEvent)

        val compiledRecipe: CompiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        assertTrue(compiledRecipe.validationErrors.isEmpty())
        compiledRecipe.interactionTransitions().foreach { transition ->
            if (transition.interactionName().equals("OptionalIngredientInteraction")) {
                assertEquals(3, transition.predefinedParameters().size())
                assertEquals(Some(NullValue), transition.predefinedParameters()["missingJavaOptional2"])
                assertEquals(Some(NullValue), transition.predefinedParameters()["missingScalaOption"])
                assertEquals(Some(NullValue), transition.predefinedParameters()["missingScalaOption2"])
            }
        }
    }

    @Test
    fun `The recipe compiler should give the correct id when it compiles a java recipe`() {
        val recipe = TestRecipeJava.getRecipe("id-test-recipe")
        val compiledRecipeKotlin = RecipeCompilerKotlin.compileRecipe(recipe)
        val compiledRecipeScala = RecipeCompiler.compileRecipe(recipe)
        assertEquals(compiledRecipeScala.recipeId(), compiledRecipeKotlin.recipeId())

        assertEquals("220827c42a75b3f8", compiledRecipeKotlin.recipeId())
    }

    @Test
    fun `The recipe compiler should give the interaction with Reprovider enabled when it compiles a java recipe and changes recipeId`() {
        val recipe = TestRecipeJava.getRecipeReprovider("id-test-recipe")
        val compiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertEquals("416e8abc02abcbee", compiledRecipe.recipeId())
    }

    @Test
    fun `The recipe compiler should give the interaction for checkpoint-events when it compiles a java recipe`() {
        val recipe = TestRecipeJava.getRecipe("id-test-recipe")
            .withCheckpointEvent(
                CheckPointEvent.apply(
                    "Success",
                    emptySet<String>().asScala,
                    emptySet<scala.collection.immutable.Set<String>>().asScala
                ).withRequiredEvent(initialEvent())
            )
        val compiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)
        assertEquals("469441173f91869a", compiledRecipe.recipeId())
        assertEquals(1, compiledRecipe.petriNet().transitions().count {
            it is InteractionTransition && it.interactionName()
                .contains("${checkpointEventInteractionPrefix}Success")
        })
    }

    @Test
    fun `give the interaction for sub-recipes when it compiles a java recipe`() {

        val subSubRecipe: Recipe = recipe("SubSubRecipe")
            .withInteractions(
                interactionOne()
                    .withEventOutputTransformer(
                        interactionOneSuccessful(),
                        mapOf("interactionOneOriginalIngredient" to "interactionOneIngredient").asScala
                    )
                    .withFailureStrategy(
                        InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
                            .withInitialDelay(10.milliseconds)
                            .withUntil(Some(UntilMaximumRetries(3)))
                            .build()
                    ),
                interactionTwo()
                    .withOverriddenIngredientName("initialIngredientOld", "initialIngredient"),
            )

        val subRecipe: Recipe = recipe("SubRecipe")
            .withInteractions(
                interactionThree()
                    .withMaximumInteractionCount(1),
                interactionFour()
                    .withRequiredEvents(secondEvent(), eventFromInteractionTwo()),
                interactionFive(),
                interactionSix(),
            )
            .withSubRecipe(subSubRecipe)

        val recipe: Recipe = recipe("Recipe")
            .withSensoryEvents(
                initialEvent(),
                initialEventExtendedName(),
                secondEvent(),
                notUsedSensoryEvent()
            )
            .withInteractions(
                providesNothingInteraction(),
                sieveInteraction()
            )
            .withSubRecipe(subRecipe)

        val compiledRecipe = RecipeCompilerKotlin.compileRecipe(recipe)

        val res = compiledRecipe.petriNet().transitions().asJava
            .flatMap {
                when (it) {
                    is InteractionTransition -> listOf(it.interactionName())
                    else -> emptyList<String>()
                }
            }
            .filter { it.startsWith(subRecipePrefix) }.toSet()

        assertEquals("ae2282f55f0a4f9f", compiledRecipe.recipeId())
        assertEquals(
            setOf(
                $$"$SubRecipe$SubSubRecipe$InteractionOne",
                $$"$SubRecipe$SubSubRecipe$InteractionTwo",
                $$"$SubRecipe$SubRecipe$InteractionThree",
                $$"$SubRecipe$SubRecipe$InteractionFour",
                $$"$SubRecipe$SubRecipe$InteractionFive",
                $$"$SubRecipe$SubRecipe$InteractionSix",
            ), res
        )
    }

    private inline fun <reified T : Throwable> assertFailsWith(
        exceptionMessage: String,
        message: String? = null,
        init: () -> Any?
    ) {
        try {
            init()
        } catch (t: Throwable) {
            if (t is T) {
                if (t.message == exceptionMessage)
                    return
                else
                    fail(message ?: "Exception ${T::class.simpleName} thrown but message is different")
            }
            fail(message ?: "Exception thrown but not ${T::class.simpleName}")
        }
        fail(message ?: "No exception thrown")
    }

    private fun recordType(recordsFields: List<RecordField>) = RecordType(recordsFields.asScala)

    private fun recipe(name: String?): Recipe = Recipe.apply(name)
    private fun event(name: String?, ingredients: List<Ingredient> = emptyList(), maxFiringLimit: Int? = null) =
        Event.apply(name, ingredients.asScala).let {
            when (maxFiringLimit) {
                null -> it
                else -> it.withMaxFiringLimit(maxFiringLimit)
            }
        }

    val recipeInstanceId = ingredient<String>(common.recipeInstanceIdName)

    fun Recipe.withInteractions(vararg newInteractions: InteractionDescriptor) =
        this.withInteractions(newInteractions.asScala as Seq<InteractionDescriptor>?)

    fun Recipe.withSensoryEvents(vararg sensoryEvent: com.ing.baker.recipe.common.Event) =
        this.withSensoryEvents(sensoryEvent.asScala as Seq<com.ing.baker.recipe.common.Event>)

    val Int.milliseconds get() = Duration.create(this.toLong(), TimeUnit.MILLISECONDS)
    val Int.seconds get() = Duration.create(this.toLong(), TimeUnit.SECONDS)

    object common {
        val recipeInstanceIdName = `package$`.`MODULE$`.recipeInstanceIdName()
        val recipeInstanceMetadataName = `package$`.`MODULE$`.recipeInstanceMetadataName()
    }

    @OptIn(ExperimentalStdlibApi::class)
    inline fun <reified T> ingredient(name: String?) = Ingredient(name, Converters.readJavaType(typeOf<T>().javaType))

    private fun interaction(
        name: String?,
        inputIngredients: List<Ingredient>,
        output: List<Event>,
        requiredEvents: Set<String> = emptySet(),
        requiredOneOfEvents: Set<Set<String>> = emptySet(),
        predefinedIngredients: Map<String, Value> = emptyMap(),
        overriddenIngredientNames: Map<String, String> = emptyMap(),
        overriddenOutputIngredientName: String? = null,
        maximumInteractionCount: Int? = null,
        failureStrategy: com.ing.baker.recipe.common.InteractionFailureStrategy? = null,
        eventOutputTransformers: Map<com.ing.baker.recipe.common.Event, EventOutputTransformer> = emptyMap(),
        isReprovider: Boolean = false,
        oldName: String? = null,
    ): Interaction =
        `Interaction$`.`MODULE$`.apply(
            name,
            inputIngredients.asScala,
            output.asScala,
            requiredEvents.asScala,
            requiredOneOfEvents.map { it: Set<String> -> it.asScala }.toSet().asScala,
            predefinedIngredients.asScala,
            overriddenIngredientNames.asScala,
            Option.apply(overriddenOutputIngredientName),
            Option.apply(maximumInteractionCount),
            Option.apply(failureStrategy),
            eventOutputTransformers.asScala,
            isReprovider,
            Option.apply(oldName)
        )

    // Ugly Scala glue
    val Int32 = `Int32$`.`MODULE$`
    val NullValue = `NullValue$`.`MODULE$`
    val checkpointEventInteractionPrefix = com.ing.baker.il.`package$`.`MODULE$`.checkpointEventInteractionPrefix()
    val subRecipePrefix = com.ing.baker.il.`package$`.`MODULE$`.subRecipePrefix()

    fun Interaction.withPredefinedIngredients(vararg ingredients: Pair<String, Any?>) =
        this.withPredefinedIngredients(ingredients.map {
            Tuple2(
                it.first,
                it.second
            )
        }.asScala)

    fun Interaction.withRequiredEvents(vararg events: com.ing.baker.recipe.common.Event) =
        this.withRequiredEvents(events.toList().asScala)

    object InteractionFailureStrategy {
        object RetryWithIncrementalBackoff {
            fun builder() =
                com.ing.baker.recipe.common.`InteractionFailureStrategy$RetryWithIncrementalBackoff$builder$`.`MODULE$`.apply()
        }
    }

    object UntilDeadline {
        operator fun invoke(duration: Duration) =
            com.ing.baker.recipe.common.`InteractionFailureStrategy$RetryWithIncrementalBackoff$UntilDeadline$`.`MODULE$`.apply(
                duration
            )

    }

    object UntilMaximumRetries {
        operator fun invoke(maxRetries: Int) =
            com.ing.baker.recipe.common.`InteractionFailureStrategy$RetryWithIncrementalBackoff$UntilMaximumRetries$`.`MODULE$`.apply(
                maxRetries
            )
    }
}
