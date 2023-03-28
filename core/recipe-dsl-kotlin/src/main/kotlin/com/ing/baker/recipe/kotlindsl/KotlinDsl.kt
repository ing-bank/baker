package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction
import com.ing.baker.recipe.javadsl.InteractionFailureStrategy
import scala.Option
import java.util.*
import kotlin.reflect.KClass
import kotlin.reflect.full.functions
import kotlin.reflect.full.primaryConstructor
import kotlin.reflect.jvm.javaType
import kotlin.time.Duration
import kotlin.time.toJavaDuration

@DslMarker
annotation class RecipeDslMarker

/**
 * Creates a [Recipe] with the given [name] and [configuration] provided through the [RecipeBuilder] receiver.
 *
 * @see RecipeBuilder
 */
fun recipe(name: String, configuration: (RecipeBuilder.() -> Unit) = {}): Recipe {
    return RecipeBuilder(name).apply(configuration).build()
}

@RecipeDslMarker
class RecipeBuilder(private val name: String) {
    var defaultFailureStrategy: InteractionFailureStrategyBuilder? = null
    var eventReceivePeriod: Duration? = null
    var retentionPeriod: Duration? = null

    @PublishedApi
    internal val interactions: MutableSet<Interaction> = mutableSetOf()

    private val sensoryEvents: MutableSet<Event> = mutableSetOf()

    /**
     * Registers sensory events to the recipe via the [SensoryEventsBuilder] receiver.
     *
     * @see SensoryEventsBuilder
     */
    fun sensoryEvents(init: SensoryEventsBuilder.() -> Unit) {
        sensoryEvents.addAll(SensoryEventsBuilder().apply(init).build())
    }

    /**
     * Registers an interaction [T] to the recipe. Additional [configuration] can be provided via
     * the [InteractionBuilder] receiver.
     *
     * @see InteractionBuilder
     */
    inline fun <reified T : com.ing.baker.recipe.javadsl.Interaction> interaction(configuration: (InteractionBuilder.() -> Unit) = {}) {
        interactions.add(InteractionBuilder(T::class).apply(configuration).build())
    }

    fun retryWithIncrementalBackoff(init: RetryWithIncrementalBackoffBuilder.() -> Unit): InteractionFailureStrategyBuilder {
        return RetryWithIncrementalBackoffBuilder().apply(init)
    }

    fun blockInteraction(): InteractionFailureStrategyBuilder {
        return BlockInteractionBuilder
    }

    fun fireEventAfterFailure(eventName: String): InteractionFailureStrategyBuilder {
        return FireEventAfterFailureBuilder(eventName)
    }

    inline fun <reified T> fireEventAfterFailure(): InteractionFailureStrategyBuilder {
        return FireEventAfterFailureBuilder(T::class.simpleName!!)
    }

    internal fun build() = Recipe(
        name,
        interactions.toList(),
        sensoryEvents.toList(),
        defaultFailureStrategy?.build() ?: BlockInteractionBuilder.build(),
        Optional.ofNullable(eventReceivePeriod?.toJavaDuration()),
        Optional.ofNullable(retentionPeriod?.toJavaDuration())
    )
}

private fun KClass<*>.interactionFunction() = functions.single { it.name == "apply" }

@PublishedApi
internal data class EventTransformation(
    val from: KClass<*>,
    val to: String,
    val ingredientRenames: Map<String, String>
)

@RecipeDslMarker
class InteractionBuilder(private val interactionClass: KClass<*>) {
    var name: String? = null
    var maximumInteractionCount: Int? = null
    var failureStrategy: InteractionFailureStrategyBuilder? = null

    @PublishedApi
    internal val eventTransformations: MutableSet<EventTransformation> = mutableSetOf()

    private val preDefinedIngredients = mutableMapOf<String, Any>()
    private val ingredientNameOverrides = mutableMapOf<String, String>()
    private val events = mutableSetOf<KClass<*>>()
    private val requiredEvents: MutableSet<String> = mutableSetOf()
    private val requiredOneOfEvents: MutableSet<Set<String>> = mutableSetOf()

    init {
        val applyFn = interactionClass.interactionFunction()
        val sealedSubclasses = (applyFn.returnType.classifier as KClass<*>).sealedSubclasses
        if (sealedSubclasses.isNotEmpty()) {
            events.addAll(sealedSubclasses.toSet())
        } else {
            events.addAll(setOf(applyFn.returnType.classifier as KClass<*>))
        }
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

    fun ingredientNameOverrides(init: IngredientNameOverridesBuilder.() -> Unit) {
        ingredientNameOverrides.putAll(IngredientNameOverridesBuilder().apply(init).build())
    }

    inline fun <reified T> transformEvent(newName: String, init: (IngredientRenamesBuilder.() -> Unit) = {}) {
        eventTransformations.add(
            EventTransformation(
                from = T::class,
                to = newName,
                ingredientRenames = IngredientRenamesBuilder().apply(init).build()
            )
        )
    }

    fun retryWithIncrementalBackoff(init: RetryWithIncrementalBackoffBuilder.() -> Unit): InteractionFailureStrategyBuilder {
        return RetryWithIncrementalBackoffBuilder().apply(init)
    }

    fun blockInteraction(): InteractionFailureStrategyBuilder {
        return BlockInteractionBuilder
    }

    fun fireEventAfterFailure(eventName: String): InteractionFailureStrategyBuilder {
        return FireEventAfterFailureBuilder(eventName)
    }

    inline fun <reified T> fireEventAfterFailure(): InteractionFailureStrategyBuilder {
        return FireEventAfterFailureBuilder(T::class.simpleName!!)
    }

    @PublishedApi
    internal fun build(): Interaction {
        val inputIngredients = interactionClass.interactionFunction().parameters.drop(1)
            .map { Ingredient(it.name, it.type.javaType) }
            .toSet()

        val outputEvents: Set<Event> = events
            .map { it.toEvent() }
            .toSet()

        val eventTransformationsInput: Map<Event, EventOutputTransformer> =
            eventTransformations.associate { it.from.toEvent() to EventOutputTransformer(it.to, it.ingredientRenames) }

        return Interaction(
            name ?: interactionClass.simpleName!!,
            inputIngredients,
            outputEvents,
            requiredEvents,
            requiredOneOfEvents,
            preDefinedIngredients,
            ingredientNameOverrides,
            eventTransformationsInput,
            Optional.ofNullable(maximumInteractionCount),
            failureStrategy?.build() ?: BlockInteraction()
        )
    }
}

@RecipeDslMarker
class PredefinedIngredientsBuilder {
    private val preDefinedIngredients: MutableMap<String, Any> = mutableMapOf()

    infix fun String.to(value: Any) {
        preDefinedIngredients[this] = value
    }

    internal fun build() = preDefinedIngredients.toMap()
}

@RecipeDslMarker
class IngredientRenamesBuilder {
    private val ingredientRenames: MutableMap<String, String> = mutableMapOf()

    infix fun String.to(value: String) {
        ingredientRenames[this] = value
    }

    @PublishedApi
    internal fun build() = ingredientRenames.toMap()
}

@RecipeDslMarker
class IngredientNameOverridesBuilder {
    private val ingredientNameOverrides: MutableMap<String, String> = mutableMapOf()

    infix fun String.to(value: String) {
        ingredientNameOverrides[this] = value
    }

    internal fun build() = ingredientNameOverrides.toMap()
}

@RecipeDslMarker
class InteractionRequiredEventsBuilder {
    @PublishedApi
    internal val events = mutableSetOf<String>()

    inline fun <reified T> event() {
        events.add(T::class.simpleName!!)
    }

    fun event(name: String) {
        events.add(name)
    }

    internal fun build() = events.toSet()
}

@RecipeDslMarker
class InteractionRequiredOneOfEventsBuilder {
    @PublishedApi
    internal val events = mutableSetOf<String>()

    inline fun <reified T> event() {
        events.add(T::class.simpleName!!)
    }

    fun event(name: String) {
        events.add(name)
    }

    internal fun build() = events.toSet()
}

@RecipeDslMarker
class SensoryEventsBuilder {
    @PublishedApi
    internal val events = mutableMapOf<KClass<*>, Int?>()

    inline fun <reified T> event(maxFiringLimit: Int = 1) {
        events[T::class] = maxFiringLimit
    }

    inline fun <reified T> eventWithoutFiringLimit() {
        events[T::class] = null
    }

    internal fun build() = events.map { it.key.toEvent(it.value) }
}

private fun KClass<*>.toEvent(maxFiringLimit: Int? = null): Event {
    return Event(
        simpleName,
        primaryConstructor?.parameters?.map {
            Ingredient(
                it.name,
                it.type.javaType
            )
        },
        Optional.ofNullable(maxFiringLimit)
    )
}

sealed interface InteractionFailureStrategyBuilder {
    fun build(): com.ing.baker.recipe.common.InteractionFailureStrategy
}

object BlockInteractionBuilder : InteractionFailureStrategyBuilder {
    override fun build(): com.ing.baker.recipe.common.InteractionFailureStrategy =
        BlockInteraction()
}

class FireEventAfterFailureBuilder(private val eventName: String) : InteractionFailureStrategyBuilder {
    override fun build(): com.ing.baker.recipe.common.InteractionFailureStrategy =
        com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAfterFailure(Option.apply(eventName))
}

@RecipeDslMarker
class RetryWithIncrementalBackoffBuilder : InteractionFailureStrategyBuilder {

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

    override fun build(): com.ing.baker.recipe.common.InteractionFailureStrategy =
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
                    is RetryWithIncrementalBackoffBuilder.Deadline -> (until as RetryWithIncrementalBackoffBuilder.Deadline).duration.let {
                        withDeadline(
                            it.toJavaDuration()
                        )
                    }

                    is RetryWithIncrementalBackoffBuilder.MaximumRetries -> (until as RetryWithIncrementalBackoffBuilder.MaximumRetries).count.let {
                        withMaximumRetries(
                            it
                        )
                    }
                }
            }
            .build()
}
