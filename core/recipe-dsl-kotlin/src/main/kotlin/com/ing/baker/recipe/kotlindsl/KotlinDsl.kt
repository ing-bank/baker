package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common.Ingredient
import com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction
import com.ing.baker.recipe.javadsl.Event
import com.ing.baker.recipe.javadsl.InteractionFailureStrategy
import com.ing.baker.types.Converters
import scala.Option
import java.util.*
import kotlin.jvm.internal.CallableReference
import kotlin.reflect.KClass
import kotlin.reflect.KFunction
import kotlin.reflect.jvm.javaType
import kotlin.time.Duration
import kotlin.time.toJavaDuration


@DslMarker
@Target(AnnotationTarget.CLASS, AnnotationTarget.TYPE)
annotation class Scoped

fun convertRecipe(builder: RecipeBuilder): Recipe {
    return Recipe(
        builder.name,
        builder.interactions.map(::interactionFunctionToCommonInteraction).toList(),
        builder.sensoryEvents.map { it.kClass.java }.toList(),
        builder.defaultFailureStrategy.convert(),
        Optional.empty(),
        Optional.empty(),
    )
}

fun recipe(name: String, init: (RecipeBuilder.() -> Unit)? = null): RecipeBuilder {
    val builder = RecipeBuilder()
    builder.name = name
    init?.apply {
        builder.apply(this)
    }
    return builder
}

@Scoped
class RecipeBuilder {

    lateinit var name: String
    var interactions: Set<InteractionBuilder> = emptySet()
    var sensoryEvents: Set<KotlinEvent> = emptySet()
    var defaultFailureStrategy: FailureStrategyBuilder? = null

    fun interactions(init: InteractionsBuilder.() -> Unit) {
        val builder = InteractionsBuilder()
        builder.apply(init)
        this.interactions = builder.build()
    }

    fun sensoryEvents(init: SensoryEventsBuilder.() -> Unit) {
        sensoryEvents = SensoryEventsBuilder().apply(init).build()
    }

    fun defaultFailureStrategy(init: FailureStrategyBuilder.() -> Unit) {
        defaultFailureStrategy = FailureStrategyBuilder().apply(init)
    }
}

fun interactionFunctionToCommonInteraction(builder: InteractionBuilder): Interaction {
    val inputIngredients = builder.func.parameters.drop(1)
        .map {
            val type = Converters.readJavaType(it.type.javaType)
            Ingredient(it.name, type)
        }

    val events: Set<com.ing.baker.recipe.common.Event> = builder.events
        .map { Event(it.java, Option.empty()) }
        .toSet()

    return Interaction(
        builder.func.ownerClass().simpleName ?: "",
        HashSet(inputIngredients),
        HashSet(events),
        HashSet(builder.requiredEvents.map { it.name }),
        builder.failureStrategy.convert()
    )
}

fun FailureStrategyBuilder?.convert(): com.ing.baker.recipe.common.InteractionFailureStrategy = this
    ?.run {
        InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder()
            .run {
                backoffFactor?.let { withBackoffFactor(it) } ?: this
            }
            .run {
                initialDelay?.let { withInitialDelay(it.toJavaDuration()) } ?: this
            }
            .run {
                maxTimeBetweenRetries?.let { withMaxTimeBetweenRetries(it.toJavaDuration()) }
                    ?: this
            }
            .run {
                fireRetryExhaustedEvent?.let { withFireRetryExhaustedEvent(it) } ?: this
            }
            .run {
                when (until) {
                    is FailureStrategyBuilder.Deadline -> (until as FailureStrategyBuilder.Deadline).duration.let {
                        withDeadline(
                            it.toJavaDuration()
                        )
                    }

                    is FailureStrategyBuilder.MaximumRetries -> (until as FailureStrategyBuilder.MaximumRetries).count.let {
                        withMaximumRetries(
                            it
                        )
                    }
                }
            }
            .build()
    }
    ?: BlockInteraction()

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

data class EventTransformation(
    val from: KClass<*>,
    val to: String,
    val ingredientRenames: Map<String, String>
)

@Scoped
class InteractionBuilder {
    var name: String? = null
    var maximumInteractionCount: Int? = null

    // TODO varargs not possible here, probably can be nicer
    var preDefinedIngredients = mutableMapOf<String, String>()

    lateinit var func: KFunction<*>
    var events: Set<KClass<*>> = setOf()

    val eventTransformations: MutableSet<EventTransformation> = mutableSetOf()
    val requiredEvents: MutableSet<InteractionEvent> = mutableSetOf()
    val requiredOneOfEvents: MutableSet<Set<InteractionEvent>> = mutableSetOf() // TODO actually use this somewhere

    var failureStrategy: FailureStrategyBuilder? = null

    fun func(func: KFunction<*>) {
        val sealedSubclasses = (func.returnType.classifier as KClass<*>).sealedSubclasses
        if (sealedSubclasses.isNotEmpty()) {
            this.events = sealedSubclasses.toSet()
        } else {
            this.events = setOf(func.returnType.classifier as KClass<*>)
        }

        this.func = func
    }

    fun requiredEvents(init: InteractionRequiredEventsBuilder.() -> Unit) {
        requiredEvents.addAll(InteractionRequiredEventsBuilder().apply(init).build())
    }

    fun requiredOneOfEvents(init: InteractionRequiredOneOfEventsBuilder.() -> Unit) {
        requiredOneOfEvents.add(InteractionRequiredOneOfEventsBuilder().apply(init).build())
    }

    fun preDefinedIngredients(init: PredefinedIngredientsBuilder.() -> Unit) {
        preDefinedIngredients.putAll(PredefinedIngredientsBuilder().apply(init).build())
    }

    // TODO Investigate if we can improve on this with vararg
    inline fun <reified T> transformEvent(to: String, ingredientRenames: Map<String, String> = emptyMap()) {
        eventTransformations.add(
            EventTransformation(T::class, to, ingredientRenames)
        )
    }

    fun failureStrategy(init: FailureStrategyBuilder.() -> Unit) {
        this.failureStrategy = FailureStrategyBuilder().apply(init)
    }
}

@Scoped
class PredefinedIngredientsBuilder {
    private val preDefinedIngredients: MutableMap<String, String> = mutableMapOf()

    infix fun String.to(value: String) {
        preDefinedIngredients[this] = value
    }

    fun build() = preDefinedIngredients.toMap()
}

// TODO fix this
data class InteractionEvent(val name: String)

@Scoped
class InteractionRequiredEventsBuilder {
    val events = mutableSetOf<InteractionEvent>()

    // TODO not null assertion...
    inline fun <reified T> event() {
        events.add(InteractionEvent(T::class.simpleName!!))
    }

    fun event(name: String) {
        events.add(InteractionEvent(name))
    }

    fun build() = events.toSet()
}

@Scoped
class InteractionRequiredOneOfEventsBuilder {
    val events = mutableSetOf<InteractionEvent>()

    // TODO not null assertion...
    inline fun <reified T> event() {
        events.add(InteractionEvent(T::class.simpleName!!))
    }

    fun event(name: String) {
        events.add(InteractionEvent(name))
    }

    fun build() = events.toSet()
}

@Scoped
class SensoryEventsBuilder {
    val events = mutableSetOf<KotlinEvent>()

    inline fun <reified T> event(maxFiringLimit: Int? = null) = events.add(KotlinEvent(T::class, maxFiringLimit))

    fun build() = events.toSet()
}

@Scoped
class FailureStrategyBuilder {

    sealed interface Until
    data class Deadline(val duration: Duration) : Until
    data class MaximumRetries(val count: Int) : Until

    lateinit var until: Until

    var initialDelay: Duration? = null
    var maxTimeBetweenRetries: Duration? = null
    var backoffFactor: Double? = null
    var fireRetryExhaustedEvent: String? = null

    fun deadline(duration: Duration) = Deadline(duration)
    fun maximumRetries(count: Int) = MaximumRetries(count)
}

// Temp class for experimentation purposes. Probably should map this to some common Event class.
// We can get ingredients from a KClass via .primaryConstructor?.parameters?.map { Pair(it.name, it.type) }
data class KotlinEvent(val kClass: KClass<*>, val maxFiringLimit: Int?)
