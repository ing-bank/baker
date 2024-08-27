package com.ing.baker.runtime.kotlindsl

import com.ing.baker.runtime.model.recipeinstance.RecipeInstance
import scala.Option
import scala.concurrent.duration.FiniteDuration
import scala.jdk.CollectionConverters
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

data class RecipeInstanceConfig(
        val idleTTL: Duration? = 5.seconds,
        val ingredientsFilter: List<String> = emptyList()) {

    private fun Duration.toFiniteDuration(): FiniteDuration {
        return FiniteDuration.fromNanos(this.inWholeNanoseconds)
    }
    fun toBakerFRecipeInstanceConfig(): RecipeInstance.Config {
        return RecipeInstance.Config(
                idleTTL?.let{ Option.apply(it.toFiniteDuration()) } ?: Option.empty(),
                CollectionConverters.ListHasAsScala(ingredientsFilter).asScala().toSeq()
        )
    }
}