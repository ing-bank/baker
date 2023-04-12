package com.ing.baker.runtime.kotlindsl

import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.javadsl.Baker
import kotlinx.coroutines.future.await

class Baker(private val jBaker: Baker) : AutoCloseable {
    override fun close() {
        // FIXME we should block here and wait for a max of 10 seconds
        jBaker.gracefulShutdown()
    }

    suspend fun addRecipe(recipeRecord: RecipeRecord): String = jBaker.addRecipe(recipeRecord).await()
    
}