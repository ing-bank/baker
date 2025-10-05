package com.ing.baker.compiler

import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.recipe.kotlindsl.recipe
import com.ing.baker.types.NullValue
import com.ing.baker.types.`NullValue$`
import org.junit.Assert.assertEquals
import org.junit.Assert.assertTrue
import org.junit.Assert.fail
import org.junit.Test
import java.util.Optional

class RecipeCompilerTest {

    class EventA

    interface InteractionA : Interaction {
        sealed interface ReserveItemsOutcome
        class ItemsReserved(val reservedItems: List<String>) : ReserveItemsOutcome
        class OrderHadUnavailableItems(val unavailableItems: List<String>) : ReserveItemsOutcome

        fun apply(
            orderId: String,
            items: List<String>
        ): ReserveItemsOutcome
    }

    @Test
    fun `should compile dsl to recipe`() {

        val recipe = recipe("recipe") {
            sensoryEvents {
                event<EventA>()
            }
            interaction<InteractionA>()
        }

        val compiled = RecipeCompiler.compileRecipe(recipe)

        assertEquals("796a3cb3eb68b35d", compiled.recipeId())
    }


    @Test
    fun `should compile dsl to recipe ingredient`() {

        val recipe = recipe("recipe") {
            sensoryEvents {
                event<EventA>()
            }
            interaction<InteractionA>()
            ingredient<String, String>("extract") @JvmSerializableLambda {"Hello123"}
        }

        val compiled = RecipeCompiler.compileRecipe(recipe)

        assertEquals("ec448bcd08163a73", compiled.recipeId())
    }

    @Test
    fun `optional ingredient with name override should be handled correctly`() {
        // 1. Define the recipe using the Kotlin DSL
        val recipe = recipe("optionalIngredientOverrideRecipe") {
            interaction<InteractionWithOptionalIngredient> {
                name = "TestInteractionWithOverride"
                ingredientNameOverrides {
                    "optionalIngredient" to "overriddenOptionalIngredientName"
                }
            }
        }

        // 2. Compile the recipe
        val compiledRecipe = com.ing.baker.compiler.RecipeCompiler.compileRecipe(recipe)

        // 3. Find the specific interaction transition in the compiled recipe
        val interactionTransition = compiledRecipe.petriNet().transitions()
            .find { it is com.ing.baker.il.petrinet.InteractionTransition && it.interactionName() == "TestInteractionWithOverride" }

        // Assert that the transition was found
        if (interactionTransition == null) {
            fail("InteractionTransition 'TestInteractionWithOverride' not found in compiled recipe")
        }

        // 4. Get the predefined parameters for the interaction
        val predefinedParams = (interactionTransition.get() as com.ing.baker.il.petrinet.InteractionTransition).predefinedParameters()

        // 5. Assert that the overridden optional ingredient is present with a NullValue
        val overriddenParamValue = predefinedParams.get("overriddenOptionalIngredientName")

        assertTrue("The overridden optional ingredient should be a predefined parameter", overriddenParamValue.isDefined)
    }

    // Helper interaction for the test
    interface InteractionWithOptionalIngredient : Interaction {
        class Outcome

        fun apply(
            mandatoryIngredient: String,
            optionalIngredient: Optional<String>
        ): Outcome
    }
}