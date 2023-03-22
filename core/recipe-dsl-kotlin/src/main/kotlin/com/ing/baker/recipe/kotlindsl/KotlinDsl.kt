package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction
import com.ing.baker.recipe.javadsl.InteractionFailureStrategy
import scala.Option
import java.util.*
import kotlin.jvm.internal.CallableReference
import kotlin.reflect.KClass
import kotlin.reflect.KFunction
import kotlin.reflect.full.primaryConstructor
import kotlin.reflect.jvm.javaType
import kotlin.time.Duration
import kotlin.time.toJavaDuration

@DslMarker
@Target(AnnotationTarget.CLASS, AnnotationTarget.TYPE)
annotation class Scoped

fun convertRecipe(builder: RecipeBuilder): Recipe {
    return Recipe(
        builder.name,
        builder.interactions.map { it.convert() }.toList(),
        builder.sensoryEvents.map { it.convert() }.toList(),
        builder.defaultFailureStrategy?.convert() ?: BlockInteraction(),
        Optional.ofNullable(builder.eventReceivePeriod?.toJavaDuration()),
        Optional.ofNullable(builder.retentionPeriod?.toJavaDuration()),
    )
}

fun recipe(name: String, init: (RecipeBuilder.() -> Unit) = {}): RecipeBuilder {
    val builder = RecipeBuilder()
    builder.name = name
    builder.apply(init)
    return builder
}

@Scoped
class RecipeBuilder {

    lateinit var name: String
    var interactions: Set<InteractionBuilder> = emptySet()
    var sensoryEvents: Set<SensoryEvent> = emptySet()
    var defaultFailureStrategy: InteractionFailureStrategyBuilder? = null
    var eventReceivePeriod: Duration? = null
    var retentionPeriod: Duration? = null

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

    fun sensoryEvents(init: SensoryEventsBuilder.() -> Unit) {
        sensoryEvents = SensoryEventsBuilder().apply(init).build()
    }

    fun retryWithIncrementalBackoff(init: RetryWithIncrementalBackoffBuilder.() -> Unit): InteractionFailureStrategyBuilder {
        return RetryWithIncrementalBackoffBuilder().apply(init)
    }

    fun blockInteraction(init: BlockInteractionBuilder.() -> Unit): InteractionFailureStrategyBuilder {
        return BlockInteractionBuilder.apply(init)
    }

    fun fireEventAfterFailure(eventName: String): InteractionFailureStrategyBuilder {
        return FireEventAfterFailureBuilder(eventName)
    }

    inline fun <reified T> fireEventAfterFailure(): InteractionFailureStrategyBuilder {
        return FireEventAfterFailureBuilder(T::class.simpleName!!)
    }
}


fun InteractionBuilder.convert(): Interaction {
    val inputIngredients = func.parameters.drop(1)
        .map { Ingredient(it.name, it.type.javaType) }
        .toSet()

    val outputEvents: Set<Event> = events
        .map { it.convert() }
        .toSet()

    val eventTransformationsInput: Map<Event, EventOutputTransformer> =
        eventTransformations.associate { it.from.convert() to EventOutputTransformer(it.to, it.ingredientRenames) }

    return Interaction(
        func.ownerClass().simpleName!!,
        inputIngredients,
        outputEvents,
        requiredEvents,
        requiredOneOfEvents,
        preDefinedIngredients,
        ingredientNameOverrides,
        eventTransformationsInput,
        Optional.ofNullable(maximumInteractionCount),
        failureStrategy?.convert() ?: BlockInteraction()
    )
}

fun SensoryEvent.convert(): Event {
    return kClass.convert(maxFiringLimit)
}

fun KClass<*>.convert(maxFiringLimit: Int? = null): Event {
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

fun KFunction<*>.ownerClass(): KClass<*> {
    val owner = (this as CallableReference).owner
    return (owner as KClass<*>)
}

data class SensoryEvent(
    val kClass: KClass<*>,
    val maxFiringLimit: Int?,
)

data class EventTransformation(
    val from: KClass<*>,
    val to: String,
    val ingredientRenames: Map<String, String>
)

@Scoped
class InteractionBuilder {
    var name: String? = null
    var maximumInteractionCount: Int? = null

    var preDefinedIngredients = mutableMapOf<String, Any>()
    var ingredientNameOverrides = mutableMapOf<String, String>()

    lateinit var func: KFunction<*>
    var events: Set<KClass<*>> = setOf()

    val eventTransformations: MutableSet<EventTransformation> = mutableSetOf()
    val requiredEvents: MutableSet<String> = mutableSetOf()
    val requiredOneOfEvents: MutableSet<Set<String>> = mutableSetOf()

    var failureStrategy: InteractionFailureStrategyBuilder? = null

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

    fun blockInteraction(init: BlockInteractionBuilder.() -> Unit): InteractionFailureStrategyBuilder {
        return BlockInteractionBuilder.apply(init)
    }

    fun fireEventAfterFailure(eventName: String): InteractionFailureStrategyBuilder {
        return FireEventAfterFailureBuilder(eventName)
    }

    inline fun <reified T> fireEventAfterFailure(): InteractionFailureStrategyBuilder {
        return FireEventAfterFailureBuilder(T::class.simpleName!!)
    }
}

@Scoped
class PredefinedIngredientsBuilder {
    private val preDefinedIngredients: MutableMap<String, Any> = mutableMapOf()

    infix fun String.to(value: Any) {
        preDefinedIngredients[this] = value
    }

    fun build() = preDefinedIngredients.toMap()
}

@Scoped
class IngredientRenamesBuilder {
    private val ingredientRenames: MutableMap<String, String> = mutableMapOf()

    infix fun String.to(value: String) {
        ingredientRenames[this] = value
    }

    fun build() = ingredientRenames.toMap()
}

@Scoped
class IngredientNameOverridesBuilder {
    private val ingredientNameOverrides: MutableMap<String, String> = mutableMapOf()

    infix fun String.to(value: String) {
        ingredientNameOverrides[this] = value
    }

    fun build() = ingredientNameOverrides.toMap()
}

@Scoped
class InteractionRequiredEventsBuilder {
    val events = mutableSetOf<String>()

    inline fun <reified T> event() {
        events.add(T::class.simpleName!!)
    }

    fun event(name: String) {
        events.add(name)
    }

    fun build() = events.toSet()
}

@Scoped
class InteractionRequiredOneOfEventsBuilder {
    val events = mutableSetOf<String>()

    inline fun <reified T> event() {
        events.add(T::class.simpleName!!)
    }

    fun event(name: String) {
        events.add(name)
    }

    fun build() = events.toSet()
}

@Scoped
class SensoryEventsBuilder {
    val events = mutableSetOf<SensoryEvent>()

    inline fun <reified T> event(maxFiringLimit: Int? = null) =
        events.add(SensoryEvent(T::class, maxFiringLimit))

    fun build() = events.toSet()
}


sealed interface InteractionFailureStrategyBuilder {
    fun convert(): com.ing.baker.recipe.common.InteractionFailureStrategy
}

object BlockInteractionBuilder : InteractionFailureStrategyBuilder {
    override fun convert(): com.ing.baker.recipe.common.InteractionFailureStrategy {
        return BlockInteraction()
    }
}

class FireEventAfterFailureBuilder(private val eventName: String) : InteractionFailureStrategyBuilder {
    override fun convert(): com.ing.baker.recipe.common.InteractionFailureStrategy =
        com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAfterFailure(Option.apply(eventName))
}

@Scoped
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

    override fun convert(): com.ing.baker.recipe.common.InteractionFailureStrategy =
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
