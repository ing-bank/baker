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
 */
fun recipe(name: String, configuration: (RecipeBuilder.() -> Unit) = {}): Recipe {
    return RecipeBuilder(name).apply(configuration).build()
}

@RecipeDslMarker
class RecipeBuilder(private val name: String) {
    /**
     * The default failure strategy for interactions that don't specify a failure strategy explicitly.
     *
     * Available strategies are: [FailureStrategy.retryWithIncrementalBackoff], [FailureStrategy.fireEventAfterFailure],
     * and [FailureStrategy.blockInteraction]. Defaults to [FailureStrategy.blockInteraction].
     */
    var defaultFailureStrategy: InteractionFailureStrategyBuilder = BlockInteractionBuilder

    /**
     * The period during which the process accepts sensory events.
     *
     * TODO what does it mean when you keep the default value of null?
     */
    var eventReceivePeriod: Duration? = null

    /**
     * The period for which process data is stored.
     *
     * TODO what does it mean when you keep the default value of null?
     */
    var retentionPeriod: Duration? = null

    @PublishedApi
    internal val interactions: MutableSet<Interaction> = mutableSetOf()

    private val sensoryEvents: MutableSet<Event> = mutableSetOf()

    /**
     * Registers sensory events to the recipe via the [SensoryEventsBuilder] receiver.
     */
    fun sensoryEvents(init: SensoryEventsBuilder.() -> Unit) {
        sensoryEvents.addAll(SensoryEventsBuilder().apply(init).build())
    }

    /**
     * Registers an interaction [T] to the recipe. Additional [configuration] can be provided via
     * the [InteractionBuilder] receiver.
     */
    inline fun <reified T : com.ing.baker.recipe.javadsl.Interaction> interaction(configuration: (InteractionBuilder.() -> Unit) = {}) {
        interactions.add(InteractionBuilder(T::class).apply(configuration).build())
    }

    internal fun build() = Recipe(
        name,
        interactions.toList(),
        sensoryEvents.toList(),
        defaultFailureStrategy.build(),
        Optional.ofNullable(eventReceivePeriod?.toJavaDuration()),
        Optional.ofNullable(retentionPeriod?.toJavaDuration())
    )
}

@RecipeDslMarker
class InteractionBuilder(private val interactionClass: KClass<out com.ing.baker.recipe.javadsl.Interaction>) {
    /**
     * The name of the interaction. Defaults to the name of the interaction class.
     */
    var name: String = interactionClass.simpleName!! // Not null assertion is okay, will never be an anonymous class.

    /**
     * The maximum number of times this interaction can be invoked.
     *
     * TODO describe what happens when the maximum is reached?
     */
    var maximumInteractionCount: Int? = null

    /**
     * The failure strategy for this interaction.
     *
     * Available strategies are: [FailureStrategy.retryWithIncrementalBackoff], [FailureStrategy.fireEventAfterFailure],
     * and [FailureStrategy.blockInteraction]. Defaults to the failure strategy of the recipe.
     */
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

    /**
     * All events specified in this block have to be available for the interaction to be executed (AND precondition).
     *
     * @see requiredOneOfEvents
     */
    fun requiredEvents(init: InteractionRequiredEventsBuilder.() -> Unit) {
        requiredEvents.addAll(InteractionRequiredEventsBuilder().apply(init).build())
    }

    /**
     * One of the events specified in this block have to be available for the interaction to be
     * executed (OR precondition).
     *
     * @see requiredEvents
     */
    fun requiredOneOfEvents(init: InteractionRequiredOneOfEventsBuilder.() -> Unit) {
        requiredOneOfEvents.add(InteractionRequiredOneOfEventsBuilder().apply(init).build())
    }

    /**
     * Registers pre-defined ingredients to the recipe via the [PredefinedIngredientsBuilder] receiver.
     *
     * Example usage:
     * ```kotlin
     * preDefinedIngredients {
     *     "foo" to MyIngredient
     *     "bar" to MyOtherIngredient
     * }
     * ```
     */
    fun preDefinedIngredients(init: PredefinedIngredientsBuilder.() -> Unit) {
        preDefinedIngredients.putAll(PredefinedIngredientsBuilder().apply(init).build())
    }

    /**
     * Registers overrides of names of input ingredients via the [IngredientNameOverridesBuilder] receiver.
     *
     * Example usage:
     * ```kotlin
     * ingredientNameOverrides {
     *     "foo" to "bar"
     *     "this" to "that"
     * }
     * ```
     */
    fun ingredientNameOverrides(init: IngredientNameOverridesBuilder.() -> Unit) {
        ingredientNameOverrides.putAll(IngredientNameOverridesBuilder().apply(init).build())
    }

    /**
     * Transforms output event [T] to an event with a name of [newName]. Ingredients can be renamed via the
     * [IngredientRenamesBuilder] receiver.
     *
     * Example usage:
     * ```kotlin
     * transformEvent<MyEvent>(newName = "YourEvent") {
     *     "foo" to "bar"
     *     "this" to "that"
     * }
     * ```
     */
    inline fun <reified T> transformEvent(newName: String, init: (IngredientRenamesBuilder.() -> Unit) = {}) {
        eventTransformations.add(
            EventTransformation(
                from = T::class,
                to = newName,
                ingredientRenames = IngredientRenamesBuilder().apply(init).build()
            )
        )
    }

    @PublishedApi
    internal fun build(): Interaction {
        val inputIngredients = interactionClass.interactionFunction().parameters.drop(1)
            .map { Ingredient(it.name, it.type.javaType) }
            .toSet()

        val outputEvents: Set<Event> = events.map { it.toEvent() }.toSet()

        val eventTransformationsInput: Map<Event, EventOutputTransformer> =
            eventTransformations.associate { it.from.toEvent() to EventOutputTransformer(it.to, it.ingredientRenames) }

        return Interaction(
            name,
            inputIngredients,
            outputEvents,
            requiredEvents,
            requiredOneOfEvents,
            preDefinedIngredients,
            ingredientNameOverrides,
            eventTransformationsInput,
            Optional.ofNullable(maximumInteractionCount),
            Optional.ofNullable(failureStrategy?.build())
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

    /**
     * Registers a sensory event [T] with a [maxFiringLimit] to the recipe.
     *
     * @see eventWithoutFiringLimit
     */
    inline fun <reified T> event(maxFiringLimit: Int = 1) {
        events[T::class] = maxFiringLimit
    }

    /**
     * Registers a sensory event [T] without firing limit to the recipe.
     *
     * @see event
     */
    inline fun <reified T> eventWithoutFiringLimit() {
        events[T::class] = null
    }

    internal fun build() = events.map { it.key.toEvent(it.value) }
}

object FailureStrategy {
    /**
     * Retries interaction with an incremental backoff on failure.
     *
     * TODO write better docs for this.
     */
    fun retryWithIncrementalBackoff(init: RetryWithIncrementalBackoffBuilder.() -> Unit): InteractionFailureStrategyBuilder {
        return RetryWithIncrementalBackoffBuilder().apply(init)
    }

    /**
     * Blocks processing of interaction on failure.
     */
    fun blockInteraction(): InteractionFailureStrategyBuilder {
        return BlockInteractionBuilder
    }

    /**
     * Fires an event with a specified [name] on failure.
     */
    fun fireEventAfterFailure(name: String): InteractionFailureStrategyBuilder {
        return FireEventAfterFailureBuilder(name)
    }

    /**
     * Fires an event [T] on failure.
     */
    inline fun <reified T> fireEventAfterFailure(): InteractionFailureStrategyBuilder {
        return FireEventAfterFailureBuilder(T::class.simpleName!!)
    }
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
            .run { backoffFactor?.let { withBackoffFactor(it) } ?: this }
            .run { initialDelay?.let { withInitialDelay(it.toJavaDuration()) } ?: this }
            .run { maxTimeBetweenRetries?.let { withMaxTimeBetweenRetries(it.toJavaDuration()) } ?: this }
            .run { fireRetryExhaustedEvent?.let { withFireRetryExhaustedEvent(it) } ?: this }
            .run {
                when (until) {
                    is Deadline -> withDeadline((until as Deadline).duration.toJavaDuration())
                    is MaximumRetries -> withMaximumRetries((until as MaximumRetries).count)
                }
            }
            .build()
}

@PublishedApi
internal data class EventTransformation(
    val from: KClass<*>,
    val to: String,
    val ingredientRenames: Map<String, String>
)

private fun KClass<*>.interactionFunction() = functions.single { it.name == "apply" }

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