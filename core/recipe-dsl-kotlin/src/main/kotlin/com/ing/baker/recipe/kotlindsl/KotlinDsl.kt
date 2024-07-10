@file:OptIn(ExperimentalReflectionOnLambdas::class)

package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.annotations.FiresEvent
import com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction
import com.ing.baker.recipe.javadsl.InteractionDescriptor
import com.ing.baker.recipe.javadsl.InteractionFailureStrategy
import scala.Option
import java.lang.reflect.Type
import java.util.*
import kotlin.reflect.KClass
import kotlin.reflect.KFunction
import kotlin.reflect.full.createType
import kotlin.reflect.full.functions
import kotlin.reflect.full.primaryConstructor
import kotlin.reflect.jvm.ExperimentalReflectionOnLambdas
import kotlin.reflect.jvm.javaType
import kotlin.reflect.jvm.reflect
import kotlin.reflect.typeOf
import kotlin.time.Duration
import kotlin.time.toJavaDuration

@DslMarker
annotation class RecipeDslMarker

@RequiresOptIn(
    message = "This DSL is experimental. The API might change in the future.",
    level = RequiresOptIn.Level.WARNING
)
annotation class ExperimentalDsl

/**
 * Creates a [Recipe] with the given [name] and [configuration] provided through the [RecipeBuilder] receiver.
 */
@ExperimentalDsl
fun recipe(name: String, configuration: (RecipeBuilder.() -> Unit) = {}): Recipe {
    return RecipeBuilder(name).apply(configuration).build()
}

@RecipeDslMarker
class RecipeBuilder(private val name: String) {
    /**
     * The default failure strategy for interactions that don't specify a failure strategy explicitly.
     *
     * Available strategies are: [retryWithIncrementalBackoff], [fireEventAfterFailure], and [blockInteraction].
     * Defaults to [blockInteraction].
     */
    var defaultFailureStrategy: InteractionFailureStrategyBuilder = BlockInteractionBuilder

    /**
     * The period during which the process accepts sensory events. Defaults to accepting sensory events forever.
     */
    var eventReceivePeriod: Duration? = null

    /**
     * The period for which process data is stored. Defaults to storing process data forever.
     */
    var retentionPeriod: Duration? = null

    /**
     * Collects events and fires and new event when conditions are met.
     */
    private val checkpointEvents: MutableSet<CheckPointEvent> = mutableSetOf()

    /**
     * Collects sieve interactions.
     */
    @PublishedApi
    internal val sieves: MutableSet<Sieve> = mutableSetOf()

    @PublishedApi
    internal val interactions: MutableSet<Interaction> = mutableSetOf()

    @PublishedApi
    internal val subRecipes: MutableSet<Recipe> = mutableSetOf()

    private val sensoryEvents: MutableSet<Event> = mutableSetOf()

    /**
     * Registers sensory events to the recipe via the [SensoryEventsBuilder] receiver.
     */
    fun sensoryEvents(init: SensoryEventsBuilder.() -> Unit) {
        sensoryEvents.addAll(SensoryEventsBuilder().apply(init).build())
    }

    /**
     * Registers checkpoint events to the recipe via the [CheckpointEventBuilder] receiver.
     */
    fun checkpointEvent(eventName: String, init: CheckpointEventBuilder.() -> Unit) {
        checkpointEvents.add(CheckpointEventBuilder().apply(init).build(eventName))
    }

    /**
     * Registers an interaction [T] to the recipe. Additional [configuration] can be provided via
     * the [InteractionBuilder] receiver.
     */
    inline fun <reified T : com.ing.baker.recipe.javadsl.Interaction> interaction(configuration: (InteractionBuilder.() -> Unit) = {}) {
        interactions.add(InteractionBuilder(T::class).apply(configuration).build())
    }


    /**
     * Registers a sieve [T1, T2, R] to the recipe.
     */
    inline fun <reified T1,reified R> ingredient(name: String, noinline function: (T1) -> R) {
        val parameters = function.reflect()?.parameters ?: error("Cannot read parameters")
        val ingredients = listOf(T1::class)
            .zip(parameters)
            .map { (clazz, param) ->  Ingredient(param.name, clazz.createType().javaType) }
        addSieve(name, ingredients, typeOf<R>().javaType, function)
    }

    /**
     * Registers a sieve [T1, T2, R] to the recipe.
     */
    inline fun <reified T1, reified T2, reified R> ingredient(name: String, noinline function: (T1, T2) -> R) {
        val parameters = function.reflect()?.parameters ?: error("Cannot read parameters")
        val ingredients = listOf(T1::class, T2::class)
            .zip(parameters)
            .map { (clazz, param) ->  Ingredient(param.name, clazz.createType().javaType) }
        addSieve(name, ingredients, typeOf<R>().javaType, function)
    }

    /**
     * Registers a sieve [T1, T2, R] to the recipe.
     */
    inline fun <reified T1, reified T2, reified T3, reified R> ingredient(name: String, noinline function: (T1, T2, T3) -> R) {
        val parameters = function.reflect()?.parameters ?: error("Cannot read parameters")
        val ingredients = listOf(T1::class, T2::class, T3::class)
            .zip(parameters)
            .map { (clazz, param) ->  Ingredient(param.name, clazz.createType().javaType) }
        addSieve(name, ingredients, typeOf<R>().javaType, function)
    }

    fun addSieve(name:String, ingredients:List<Ingredient>, returnType:Type, function:Any){
        sieves.add(
            Sieve(
                name,
                ingredients,
                listOf(
                    Event(
                        "\$SieveEvent\$$name",
                        listOf(
                            Ingredient(
                                name,
                                returnType
                            )
                        ),
                        Optional.empty()
                    )
                ),
                function
            )
        )
    }

    /**
     * Registers an subrecipe [T] to the recipe. Additional [configuration] can be provided via
     * the [InteractionBuilder] receiver.
     */
    fun subRecipe(recipe: Recipe) {
        subRecipes.add(recipe)
    }


    /**
     * Retries interaction with an incremental backoff on failure.
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

    internal fun build() = Recipe(
        name,
        interactions.toList(),
        sensoryEvents.toList(),
        subRecipes.toList(),
        defaultFailureStrategy.build(),
        Optional.ofNullable(eventReceivePeriod?.toJavaDuration()),
        Optional.ofNullable(retentionPeriod?.toJavaDuration()),
        checkpointEvents,
        sieves
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
     */
    var maximumInteractionCount: Int? = null

    /**
     * The failure strategy for this interaction.
     *
     * Available strategies are: [retryWithIncrementalBackoff], [fireEventAfterFailure], and [blockInteraction].
     * Defaults to the failure strategy of the recipe.
     */
    var failureStrategy: InteractionFailureStrategyBuilder? = null

    /**
     * When this interaction is executed it will fill its own interaction places.
     * This is usefull if you want to execute this interaction multiple times without providing the ingredient again.
     * To use this the InteractionDescriptor requires a prerequisite event.
     *
     * @param isReprovider
     * @return
     */
    var isReprovider: Boolean = false

    @PublishedApi
    internal val eventTransformations: MutableSet<EventTransformation> = mutableSetOf()

    private val preDefinedIngredients = mutableMapOf<String, Any>()
    private val ingredientNameOverrides = mutableMapOf<String, String>()
    private val requiredEvents: MutableSet<String> = mutableSetOf()
    private val requiredOneOfEvents: MutableSet<Set<String>> = mutableSetOf()


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
     */
    fun preDefinedIngredients(init: PredefinedIngredientsBuilder.() -> Unit) {
        preDefinedIngredients.putAll(PredefinedIngredientsBuilder().apply(init).build())
    }

    /**
     * Registers overrides of names of input ingredients via the [IngredientNameOverridesBuilder] receiver.
     */
    fun ingredientNameOverrides(init: IngredientNameOverridesBuilder.() -> Unit) {
        ingredientNameOverrides.putAll(IngredientNameOverridesBuilder().apply(init).build())
    }

    /**
     * Transforms output event [T] to an event with a name of [newName]. Ingredients can be renamed via the
     * [IngredientRenamesBuilder] receiver.
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

    /**
     * Retries interaction with an incremental backoff on failure.
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

    @PublishedApi
    internal fun build(): Interaction {
        return if (interactionClass.interactionFunction().hasFiresEventAnnotation()) {
            val eventTransformationsInput = eventTransformations.associate {
                com.ing.baker.recipe.javadsl.Event(it.from.java, Option.empty()) to it.toEventOutputTransformer()
            }
            Interaction.of(
                name,
                InteractionDescriptor.of(interactionClass.java),
                requiredEvents,
                requiredOneOfEvents,
                preDefinedIngredients,
                ingredientNameOverrides,
                eventTransformationsInput,
                Optional.ofNullable(maximumInteractionCount),
                Optional.ofNullable(failureStrategy?.build()),
                isReprovider
            )
        } else {
            val eventTransformationsInput = eventTransformations.associate {
                it.from.toEvent() to it.toEventOutputTransformer()
            }

            val inputIngredients = interactionClass.interactionFunction().parameters.drop(1)
                .map { Ingredient(it.name, it.type.javaType) }
                .toSet()

            Interaction.of(
                name,
                interactionClass.simpleName,
                inputIngredients,
                extractOutputEvents(),
                requiredEvents,
                requiredOneOfEvents,
                preDefinedIngredients,
                ingredientNameOverrides,
                eventTransformationsInput,
                Optional.ofNullable(maximumInteractionCount),
                Optional.ofNullable(failureStrategy?.build()),
                isReprovider
            )
        }
    }

    private fun extractOutputEvents(): Set<Event> {
        val classifier = interactionClass.interactionFunction().returnType.classifier as KClass<*>
        return with(classifier) {
            if (sealedSubclasses.isNotEmpty()) {
                flattenSealedSubclasses().map { it.toEvent() }.toSet()
            } else {
                setOf(classifier.toEvent())
            }
        }
    }

    private fun KClass<*>.flattenSealedSubclasses(): List<KClass<*>> {
        return if (sealedSubclasses.isNotEmpty()) {
            sealedSubclasses.flatMap { it.flattenSealedSubclasses() }
        } else {
            listOf(this)
        }
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

@RecipeDslMarker
class CheckpointEventBuilder {

    private val requiredEvents: MutableSet<String> = mutableSetOf()
    private val requiredOneOfEvents: MutableSet<Set<String>> = mutableSetOf()

    /**
     * All events specified in this block have to be available for the checkpoint to be executed (AND precondition).
     *
     * @see requiredOneOfEvents
     */
    fun requiredEvents(init: InteractionRequiredEventsBuilder.() -> Unit) {
        requiredEvents.addAll(InteractionRequiredEventsBuilder().apply(init).build())
    }

    /**
     * One of the events specified in this block have to be available for the checkpoint to be
     * executed (OR precondition).
     *
     * @see requiredEvents
     */
    fun requiredOneOfEvents(init: InteractionRequiredOneOfEventsBuilder.() -> Unit) {
        requiredOneOfEvents.add(InteractionRequiredOneOfEventsBuilder().apply(init).build())
    }

    internal fun build(eventName: String) = CheckPointEvent(eventName, requiredEvents, requiredOneOfEvents)
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
) {
    fun toEventOutputTransformer() = EventOutputTransformer(to, ingredientRenames)
}

private fun <T : com.ing.baker.recipe.javadsl.Interaction> KClass<T>.interactionFunction() =
    functions.single { it.name == "apply" }

private fun KClass<*>.toEvent(maxFiringLimit: Int? = null): Event {
    return Event(
        simpleName,
        primaryConstructor?.parameters?.map { Ingredient(it.name, it.type.javaType) } ?: emptyList(),
        Optional.ofNullable(maxFiringLimit)
    )
}

private fun KFunction<*>.hasFiresEventAnnotation() = annotations.any { it.annotationClass == FiresEvent::class }
