package com.ing.baker.recipe

import scala.Option
import scala.concurrent.duration.FiniteDuration
import scala.jdk.javaapi.CollectionConverters
import kotlin.time.Duration
import kotlin.time.toKotlinDuration
import com.ing.baker.recipe.common.CheckPointEvent as ScalaCheckPointEvent
import com.ing.baker.recipe.common.Event as ScalaEvent
import com.ing.baker.recipe.common.EventOutputTransformer as ScalaEventOutputTransformer
import com.ing.baker.recipe.common.Ingredient as ScalaIngredient
import com.ing.baker.recipe.common.InteractionDescriptor as ScalaInteraction
import com.ing.baker.recipe.common.Recipe as ScalaRecipe
import com.ing.baker.recipe.common.Sieve as ScalaSieve
import scala.collection.Map as ScalaMap
import scala.collection.Seq as ScalaSeq
import scala.collection.Set as ScalaSet
import java.time.Duration as JavaDuration

fun FiniteDuration.toKotlin(): Duration = JavaDuration.ofNanos(toNanos()).toKotlinDuration()

fun ScalaRecipe.toKotlin(): Recipe =
    Recipe(
        name = name().orEmpty(),
        interactions = interactions().toKotlinInteractions(),
        sensoryEvents = sensoryEvents().toKotlinEvents(),
        subRecipes = subRecipes().toKotlinRecipes(),
        defaultFailureStrategy = defaultFailureStrategy(),
        eventReceivePeriod = eventReceivePeriod().toKotlin()?.toKotlin(),
        retentionPeriod = retentionPeriod().toKotlin()?.toKotlin(),
        checkpointEvents = checkpointEvents().toKotlinCheckPointEvents(),
        sieves = sieves().toKotlinSieves(),
    )

fun ScalaInteraction.toKotlin(): Interaction =
    Interaction(
        name = name().orEmpty(),
        oldName = originalName().orEmpty(),
        inputIngredients = inputIngredients().toKotlinIngredients(),
        output = output().toKotlinEvents(),
        requiredEvents = requiredEvents().toKotlin(),
        requiredOneOfEvents = CollectionConverters.asJava(requiredOneOfEvents()).map { it.toKotlin() }.toSet(),

        predefinedIngredients = predefinedIngredients().toKotlin(),
        overriddenIngredientNames = overriddenIngredientNames().toKotlin(),
        overriddenOutputIngredientName = overriddenOutputIngredientName().toKotlin(),
        eventOutputTransformers = eventOutputTransformers().toKotlin()
            .mapKeys { it.key.toKotlin() }
            .mapValues { it.value.toKotlin() },
        maximumInteractionCount = maximumInteractionCount().getOrElse { null },
        failureStrategy = failureStrategy().toKotlin(),
        isReprovider = isReprovider()
    )


fun ScalaIngredient.toKotlin(): Ingredient = Ingredient(name = name().orEmpty(), type = ingredientType())

fun ScalaSieve.toKotlin(): Sieve = Sieve(
    name = name().orEmpty(),
    inputIngredients = inputIngredients().toKotlinIngredients(),
    output = output().toKotlinEvents(),
    function = function(),
    javaTypes = javaTypes().toKotlinTypes()
)

fun ScalaCheckPointEvent.toKotlin(): CheckPointEvent = CheckPointEvent(
    name = name().orEmpty(),
    requiredEvents = requiredEvents().toKotlin(),
    requiredOneOfEvents = CollectionConverters.asJava(requiredOneOfEvents()).map { it.toKotlin() }.toSet(),
)

fun ScalaEventOutputTransformer.toKotlin(): EventOutputTransformer = EventOutputTransformer(
    newEventName = newEventName(),
    ingredientRenames = ingredientRenames().toKotlin()
)

fun ScalaEvent.toKotlin(): Event = Event(
    name = name().orEmpty(),
    providedIngredients = providedIngredients().toKotlinIngredients(),
    maxFiringLimit = maxFiringLimit().getOrElse { null }
)

private fun ScalaSeq<ScalaInteraction>.toKotlinInteractions(): List<Interaction> =
    CollectionConverters.asJava(this).toList().map { it.toKotlin() }

private fun ScalaSeq<ScalaEvent>.toKotlinEvents(): List<Event> = CollectionConverters.asJava(this).toList().map { it.toKotlin() }

private fun ScalaSet<ScalaEvent>.toKotlinEvents(): Set<Event> = CollectionConverters.asJava(this).map { it.toKotlin() }.toSet()

private fun ScalaSet<ScalaSieve>.toKotlinSieves(): Set<Sieve> = CollectionConverters.asJava(this).map { it.toKotlin() }.toSet()

private fun ScalaSet<ScalaRecipe>.toKotlinRecipes(): Set<Recipe> = CollectionConverters.asJava(this).map { it.toKotlin() }.toSet()

private fun ScalaSet<ScalaCheckPointEvent>.toKotlinCheckPointEvents(): Set<CheckPointEvent> =
    CollectionConverters.asJava(this).map { it.toKotlin() }.toSet()

private fun ScalaSeq<ScalaIngredient>.toKotlinIngredients(): List<Ingredient> =
    CollectionConverters.asJava(this).toList().map { it.toKotlin() }

private fun ScalaSet<String>.toKotlin(): Set<String> = CollectionConverters.asJava(this).toSet()

private fun ScalaSeq<java.lang.reflect.Type>.toKotlinTypes(): List<java.lang.reflect.Type> = CollectionConverters.asJava(this).toList()

private fun <K, V> ScalaMap<K, V>.toKotlin(): Map<K, V> = CollectionConverters.asJava(this).toMap()

private fun <T> Option<T>.toKotlin(): T? = getOrElse { null }
