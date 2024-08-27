package com.ing.baker.runtime.kotlindsl

import com.ing.baker.runtime.model.BakerF
import scala.concurrent.duration.FiniteDuration
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

data class Config(
        val allowAddingRecipeWithoutRequiringInstances: Boolean = false,
        val recipeInstanceConfig: RecipeInstanceConfig = RecipeInstanceConfig(),
        val idleTimeout: Duration = 60.seconds,
        val retentionPeriodCheckInterval: Duration = 10.seconds,
        val bakeTimeout: Duration = 10.seconds,
        val processEventTimeout: Duration = 10.seconds,
        val inquireTimeout: Duration = 60.seconds,
        val shutdownTimeout: Duration = 10.seconds,
        val addRecipeTimeout: Duration = 10.seconds,
        val executeSingleInteractionTimeout: Duration = 60.seconds) {

    private fun Duration.toFiniteDuration(): FiniteDuration {
        return FiniteDuration.fromNanos(this.inWholeNanoseconds)
    }

    fun toBakerFConfig(): BakerF.Config {
        return BakerF.Config(
                allowAddingRecipeWithoutRequiringInstances,
                recipeInstanceConfig.toBakerFRecipeInstanceConfig(),
                idleTimeout.toFiniteDuration(),
                retentionPeriodCheckInterval.toFiniteDuration(),
                bakeTimeout.toFiniteDuration(),
                processEventTimeout.toFiniteDuration(),
                inquireTimeout.toFiniteDuration(),
                shutdownTimeout.toFiniteDuration(),
                addRecipeTimeout.toFiniteDuration(),
                executeSingleInteractionTimeout.toFiniteDuration()
        )
    }
}