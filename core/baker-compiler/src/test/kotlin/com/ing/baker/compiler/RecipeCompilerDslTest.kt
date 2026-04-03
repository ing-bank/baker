package com.ing.baker.compiler

import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class RecipeCompilerDslTest {

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
    @OptIn(ExperimentalDsl::class)
    fun `should compile dsl to recipe`() {

        val recipe = recipe("recipe") {
            sensoryEvents {
                event<EventA>()
            }
            interaction<InteractionA>()
        }

        val compiled = RecipeCompiler.compileRecipe(recipe)

        assertEquals("9b2bc4caf5752697", compiled.recipeId())
    }


    @Test
    @OptIn(ExperimentalDsl::class)
    fun `should compile dsl to recipe ingredient`() {

        val recipe = recipe("recipe") {
            sensoryEvents {
                event<EventA>()
            }
            interaction<InteractionA>()
            ingredient<String, String>("extract") @JvmSerializableLambda { "Hello123" }
        }

        val compiled = RecipeCompiler.compileRecipe(recipe)

        assertEquals("4e146307a299c515", compiled.recipeId())
    }

}