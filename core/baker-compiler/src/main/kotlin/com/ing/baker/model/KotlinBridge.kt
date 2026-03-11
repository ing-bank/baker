package com.ing.baker.model

import scala.concurrent.duration.FiniteDuration
import kotlin.collections.mapKeys
import com.ing.baker.recipe.common.Event as ScalaEvent
import com.ing.baker.recipe.common.Recipe as ScalaRecipe
import com.ing.baker.recipe.common.Sieve as ScalaSieve
import com.ing.baker.recipe.common.Ingredient as ScalaIngredient
import com.ing.baker.recipe.common.EventOutputTransformer as ScalaEventOutputTransformer
import com.ing.baker.recipe.common.InteractionDescriptor as ScalaInteraction
import com.ing.baker.recipe.common.CheckPointEvent as ScalaCheckPointEvent
import scala.jdk.javaapi.CollectionConverters
import kotlin.time.Duration
import java.time.Duration as JavaDuration
import kotlin.time.toKotlinDuration

fun FiniteDuration.toKotlin(): Duration = JavaDuration.ofNanos(toNanos()).toKotlinDuration()

fun ScalaRecipe.toKotlin(): Recipe =
    Recipe(
        name = name().orEmpty(),
        interactions = CollectionConverters.asJava(interactions()).toList().map { it.toKotlin() },
        sensoryEvents = CollectionConverters.asJava(sensoryEvents()).map { it.toKotlin() }.toSet(),
        subRecipes = CollectionConverters.asJava(subRecipes()).map { it.toKotlin() }.toSet(),
        defaultFailureStrategy = defaultFailureStrategy(),
        eventReceivePeriod = eventReceivePeriod().map { it.toKotlin() }.getOrElse { null },
        retentionPeriod = retentionPeriod().map { it.toKotlin() }.getOrElse { null },
        checkpointEvents = CollectionConverters.asJava(checkpointEvents()).map { it.toKotlin() }.toSet(),
        sieves = CollectionConverters.asJava(this.sieves()).map { it.toKotlin() }.toSet(),
    )

fun ScalaInteraction.toKotlin(): Interaction =
    Interaction(
        name = name().orEmpty(),
        originalName = originalName().orEmpty(),
        inputIngredients = CollectionConverters.asJava(inputIngredients()).toList().map { it.toKotlin() },
        output = CollectionConverters.asJava(output()).map { it.toKotlin() },
        requiredEvents = CollectionConverters.asJava(requiredEvents()).toSet(),
        requiredOneOfEvents = CollectionConverters.asJava(requiredOneOfEvents()).toSet()
            .map { CollectionConverters.asJava(it).toSet() }.toSet(),
        predefinedIngredients = CollectionConverters.asJava(predefinedIngredients()).toMap(),
        overriddenIngredientNames = CollectionConverters.asJava(overriddenIngredientNames()).toMap(),
        overriddenOutputIngredientName = overriddenOutputIngredientName().getOrElse { null },
        eventOutputTransformers = CollectionConverters.asJava(eventOutputTransformers()).toMap()
            .mapKeys { it.key.toKotlin() }
            .mapValues { it.value.toKotlin() },
        maximumInteractionCount = maximumInteractionCount().getOrElse { null },
        failureStrategy = failureStrategy().getOrElse { null },
        isReprovider = isReprovider()
    )


fun ScalaIngredient.toKotlin(): Ingredient = Ingredient(name = name().orEmpty(), type = ingredientType())

fun ScalaSieve.toKotlin(): Sieve = Sieve(
    name = name().orEmpty(),
    inputIngredients = CollectionConverters.asJava(inputIngredients()).toList().map { it.toKotlin() },
    output = CollectionConverters.asJava(output()).map { it.toKotlin() },
    function = function(),
    javaTypes = CollectionConverters.asJava(javaTypes()).toList()
)

fun ScalaCheckPointEvent.toKotlin(): CheckPointEvent = CheckPointEvent(
    name = name().orEmpty(),
    requiredEvents = CollectionConverters.asJava(requiredEvents()).toSet(),
    requiredOneOfEvents = CollectionConverters.asJava(requiredOneOfEvents()).toSet()
        .map { CollectionConverters.asJava(it).toSet() }.toSet()
)

fun ScalaEventOutputTransformer.toKotlin(): EventOutputTransformer = EventOutputTransformer(
    newEventName = newEventName(),
    ingredientRenames = CollectionConverters.asJava(ingredientRenames()).toMap()
)

fun ScalaEvent.toKotlin(): Event = Event(
    name = name().orEmpty(),
    providedIngredients = CollectionConverters.asJava(providedIngredients()).toList().map { it.toKotlin() },
    maxFiringLimit = maxFiringLimit().getOrElse { null }
)
