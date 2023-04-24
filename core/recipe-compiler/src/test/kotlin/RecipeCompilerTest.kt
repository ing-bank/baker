package com.ing.baker.compiler

import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.recipe.kotlindsl.recipe
import org.junit.Assert.assertEquals
import org.junit.Test

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
    fun `should compile dsl to recipe without interactions`() {

        val recipe = recipe("recipe") {
            sensoryEvents {
                event<EventA>(maxFiringLimit = 1)
            }
        }

        val compiled = RecipeCompiler.compileRecipe(recipe)

        assertEquals(compiled.validationErrors.size, 1)
        assertEquals(compiled.validationErrors[0], "No interactions found.")
        assertEquals("bb928e13daf86557", compiled.recipeId())
    }

    @Test
    fun `should compile with negative firing limit and give validation error`() {

        val recipe = recipe("recipe") {
            sensoryEvents {
                event<EventA>(maxFiringLimit = -1)
            }
        }

        val compiled = RecipeCompiler.compileRecipe(recipe)

        assertEquals(compiled.validationErrors.size, 2)
        assertEquals(compiled.validationErrors[0], "No interactions found.")
        assertEquals(compiled.validationErrors[1], "MaxFiringLimit should be greater than 0")
        assertEquals("5142418ff252df08", compiled.recipeId())
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

}