package com.ing.baker.compiler

import com.ing.baker.recipe.kotlindsl.recipe
import org.junit.Test

import org.junit.Assert.assertEquals
import scala.collection.immutable.`ArraySeq$`

class RecipeCompilerTest {

    class EventA

    @Test
    fun `should compile dsl to recipe`() {

        val recipe = recipe("recipe") {
            sensoryEvents {
                event<EventA>(maxFiringLimit = 1)
            }
        }

        val compiled = RecipeCompiler.compileRecipe(recipe)

        assertEquals("bb928e13daf86557", compiled.recipeId())
    }

}