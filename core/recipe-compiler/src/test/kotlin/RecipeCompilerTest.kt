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
            ingredient<String, String>("extract"){"Hello123"}
        }

        val compiled = RecipeCompiler.compileRecipe(recipe)

        assertEquals("ec448bcd08163a73", compiled.recipeId())
    }

}