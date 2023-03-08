package com.ing.baker.recipe.kotlindsl

import com.example.demo.ScalaExtensions.toScalaMap
import com.example.demo.ScalaExtensions.toScalaSeq
import com.example.demo.ScalaExtensions.toScalaSet
import com.ing.baker.recipe.common.EventOutputTransformer
import com.ing.baker.recipe.common.Ingredient
import com.ing.baker.recipe.javadsl.Event
import com.ing.baker.recipe.javadsl.InteractionDescriptor
import com.ing.baker.recipe.javadsl.InteractionFailureStrategy
import com.ing.baker.recipe.javadsl.Recipe
import com.ing.baker.types.Converters
import com.ing.baker.types.Value
import scala.Option
import kotlin.jvm.internal.CallableReference
import kotlin.reflect.KClass
import kotlin.reflect.KFunction
import kotlin.reflect.jvm.javaType
import kotlin.time.Duration
import kotlin.time.toJavaDuration


@DslMarker
@Target(AnnotationTarget.CLASS, AnnotationTarget.TYPE)
annotation class Scoped

fun interactionFunctionToCommonInteraction(builder: InteractionBuilder): InteractionDescriptor {
    val inputIngredients = builder.func.parameters.drop(1)
        .map {
            val type = Converters.readJavaType(it.type.javaType)
            Ingredient(it.name, type)
        }

    return InteractionDescriptor(
        builder.func.ownerClass().simpleName,
        inputIngredients.toScalaSeq(),
        builder.events.map { Event(it.java, Option.empty()) }.toScalaSeq(),
        builder.requiredEvents.map { it.java.simpleName }.toScalaSet(),
        setOf<scala.collection.immutable.Set<String>>().toScalaSet(),
        mapOf<String, Value>().toScalaMap(),
        mapOf<String, String>().toScalaMap(),
        Option.empty(),
        Option.empty(),
        Option.empty(),
        mapOf<com.ing.baker.recipe.common.Event, EventOutputTransformer>().toScalaMap(),
        Option.empty(),
    )
}

fun convertRecipe(builder: RecipeBuilder): Recipe {
    return Recipe(builder.name)
        .withInteractions(builder.interactions.map(::interactionFunctionToCommonInteraction).toScalaSeq())
        // TODO differentiate between events with and without firing limit.
        .withSensoryEvents(builder.sensoryEvents.map { it.kClass.java }.toScalaSeq())
        .withDefaultFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder()
            .withInitialDelay(builder.defaultFailureStrategy.initialDelay?.toJavaDuration())
            .withDeadline(builder.defaultFailureStrategy.deadline?.toJavaDuration())
            .withMaxTimeBetweenRetries(builder.defaultFailureStrategy.maxTimeBetweenRetries?.toJavaDuration())
            .build()
        )
}

fun KFunction<*>.ownerClass(): KClass<*> {
    val owner = (this as CallableReference).owner
    return (owner as KClass<*>)
}

@Scoped
class InteractionsBuilder {

    var interactions: Set<InteractionBuilder> = setOf()

    fun interaction(func: KFunction<*>) {
        val builder = InteractionBuilder()
        builder.func(func)
        interactions = interactions + builder
    }

    fun interaction(func: KFunction<*>, init: InteractionBuilder.() -> Unit) {
        val builder = InteractionBuilder()
        builder.apply(init)
        builder.func(func)
        interactions = interactions + builder
    }

    fun build() = interactions
}

@Scoped
class InteractionBuilder {

    lateinit var func: KFunction<*>
    var events: Set<KClass<*>> = setOf()
    var requiredEvents: Set<KClass<*>> = setOf()

    fun func(func: KFunction<*>) {
        val sealedSubclasses = (func.returnType.classifier as KClass<*>).sealedSubclasses
        if (sealedSubclasses.isNotEmpty()) {
            this.events = sealedSubclasses.toSet()
        } else {
            this.events = setOf(func.returnType.classifier as KClass<*>)
        }

        this.func = func
    }

    fun events(vararg events: KClass<*>) {
        this.events = events.toSet()
    }

    fun requiredEvents(vararg requiredEvents: KClass<*>) {
        this.requiredEvents = requiredEvents.toSet()
    }
}

fun recipe(name: String, init: RecipeBuilder.() -> Unit): RecipeBuilder {
    val builder = RecipeBuilder()
    builder.name = name
    builder.apply(init)
    return builder
}

@Scoped
class SensoryEventsBuilder {
    val events = mutableSetOf<KotlinEvent>()

    inline fun <reified T> event(maxFiringLimit: Int = 1) = events.add(KotlinEvent(T::class, maxFiringLimit))
    inline fun <reified T> eventWithoutFiringLimit() = events.add(KotlinEvent(T::class, null))

    fun build() = events.toSet()
}

@Scoped
class DefaultFailureStrategyBuilder {
    data class DefaultFailureStrategy(
        val initialDelay: Duration? = null,
        val deadline: Duration? = null,
        val maxTimeBetweenRetries: Duration? = null
    )

    var defaultFailureStrategy = DefaultFailureStrategy()

    fun initialDelay(initialDelay: Duration) = defaultFailureStrategy
        .copy(initialDelay = initialDelay)
        .also { this.defaultFailureStrategy = it }

    fun deadline(deadline: Duration) = defaultFailureStrategy
        .copy(deadline = deadline)
        .also { this.defaultFailureStrategy = it }

    fun maxTimeBetweenRetries(maxTimeBetweenRetries: Duration) = defaultFailureStrategy
        .copy(maxTimeBetweenRetries = maxTimeBetweenRetries)
        .also { this.defaultFailureStrategy = it }
    fun build() = defaultFailureStrategy
}


// Temp class for experimentation purposes. Probably should map this to some common Event class.
// We can get ingredients from a KClass via .primaryConstructor?.parameters?.map { Pair(it.name, it.type) }
data class KotlinEvent(val kClass: KClass<*>, val maxFiringLimit: Int?)

@Scoped
class RecipeBuilder {

    lateinit var name: String
    lateinit var interactions: Set<InteractionBuilder>
    lateinit var sensoryEvents: Set<KotlinEvent>
    lateinit var defaultFailureStrategy: DefaultFailureStrategyBuilder.DefaultFailureStrategy

    fun interactions(init: InteractionsBuilder.() -> Unit) {
        val builder = InteractionsBuilder()
        builder.apply(init)
        this.interactions = builder.build()
    }

    fun sensoryEvents(init: SensoryEventsBuilder.() -> Unit) {
        sensoryEvents = SensoryEventsBuilder().apply(init).build()
    }

    fun defaultFailureStrategy(init: DefaultFailureStrategyBuilder.() -> Unit) {
        defaultFailureStrategy = DefaultFailureStrategyBuilder().apply(init).build()
    }
}
