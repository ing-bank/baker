package com.ing.baker.openapi.dsl

import com.ing.baker.recipe.kotlindsl.Event
import com.ing.baker.recipe.kotlindsl.Ingredient
import com.ing.baker.recipe.kotlindsl.Interaction
import com.ing.baker.recipe.kotlindsl.RecipeBuilder
import community.flock.wirespec.kotlin.Wirespec
import java.util.Optional
import kotlin.reflect.KClass
import kotlin.reflect.full.memberProperties
import kotlin.reflect.full.primaryConstructor
import kotlin.reflect.jvm.javaType

@DslMarker
annotation class ApiDslMarker

/**
 * Registers a Baker interaction in this recipe based on an OpenAPI [operation].
 * The [configure] block declares status → user-event mappers and optional Baker
 * controls (required events, ingredient name overrides, maximumInteractionCount).
 */
fun RecipeBuilder.api(
    operation: ApiOperation,
    configure: ApiInteractionScope.() -> Unit,
) {
    val scope = ApiInteractionScope(operation).apply(configure)
    addInteraction(scope.buildInteraction())
    apiInteractionConfigCollector.get()?.put(
        operation.operationName,
        ApiInteractionConfig(operation, scope.configuredMappers, scope.configuredNameOverrides),
    )
}

internal data class ApiInteractionConfig(
    val operation: ApiOperation,
    val mappers: Map<Int, (Wirespec.Response<*>) -> Any>,
    val nameOverrides: Map<String, String>,
)

@ApiDslMarker
class ApiInteractionScope internal constructor(private val operation: ApiOperation) {

    @PublishedApi
    internal val mappers = mutableMapOf<Int, (Wirespec.Response<*>) -> Any>()

    @PublishedApi
    internal val outputEventClasses = mutableSetOf<KClass<*>>()

    @PublishedApi
    internal val requiredEvents = mutableSetOf<String>()

    @PublishedApi
    internal val ingredientNameOverridesMap = mutableMapOf<String, String>()

    private var maxInteractionCount: Int? = null

    /**
     * Maps responses of HTTP [status] to a user-defined event. The [mapper]
     * receives the wirespec response and returns a domain event instance.
     */
    inline fun <reified R : Wirespec.Response<*>, reified E : Any> on(
        status: Int,
        noinline mapper: (R) -> E,
    ) {
        @Suppress("UNCHECKED_CAST")
        mappers[status] = { resp -> mapper(resp as R) }
        outputEventClasses.add(E::class)
    }

    fun requires(vararg eventClasses: KClass<*>) {
        eventClasses.forEach { requiredEvents.add(it.simpleName!!) }
    }

    fun maximumInteractionCount(n: Int) {
        maxInteractionCount = n
    }

    /**
     * Maps API input field names (left) to recipe ingredient names (right).
     * Use this when the recipe's ingredient name doesn't match the API contract
     * (e.g. domain calls it `customerId`, the OpenAPI doc calls it `userId`).
     *
     * The wirespec request DTO itself is never an ingredient — only flat values
     * (path / query / header / flattened body fields) flow through Baker.
     */
    fun ingredientNameOverrides(block: IngredientNameOverridesScope.() -> Unit) {
        val scope = IngredientNameOverridesScope().apply(block)
        ingredientNameOverridesMap.putAll(scope.entries)
    }

    /**
     * Declares that [T] is the canonical input event for this API operation —
     * its constructor fields populate the API request. The block lets the
     * recipe author rename fields where event names don't match API names:
     *
     *   inputFrom<CreateAccountCommand> {
     *       "userId" from "customerId"   // API field ← event field
     *   }
     *
     * Equivalent to `requires(T::class) + ingredientNameOverrides { ... }` with
     * the inverted-arrow `from` infix making the intent clearer (read as:
     * "the API's userId comes from the event's customerId field"). The wirespec
     * request DTO itself never appears in the recipe — only the event does.
     */
    inline fun <reified T : Any> inputFrom(noinline configure: InputFromScope.() -> Unit = {}) {
        requiredEvents.add(T::class.simpleName!!)
        val scope = InputFromScope().apply(configure)
        ingredientNameOverridesMap.putAll(scope.entries)
    }

    /** Read-only view of configured mappers, useful for app-startup binding. */
    val configuredMappers: Map<Int, (Wirespec.Response<*>) -> Any> get() = mappers.toMap()

    /** Read-only view of API field → ingredient overrides. */
    val configuredNameOverrides: Map<String, String> get() = ingredientNameOverridesMap.toMap()

    internal fun buildInteraction(): Interaction {
        val inputIngredients: Set<Ingredient> = operation.inputFields
            .map { Ingredient(it.name, it.type.java) }
            .toSet()
        val events: Set<Event> = outputEventClasses
            .map { it.toEvent() }
            .toSet()
        return Interaction.of(
            operation.operationName,
            operation.operationName,
            inputIngredients,
            events,
            requiredEvents,
            emptySet<Set<String>>(),
            emptyMap<String, Any>(),
            ingredientNameOverridesMap.toMap(),
            emptyMap(),
            Optional.ofNullable(maxInteractionCount),
            Optional.empty(),
            false,
        )
    }
}

@ApiDslMarker
class IngredientNameOverridesScope internal constructor() {
    internal val entries = mutableMapOf<String, String>()
    /** Maps the API input field name (receiver) to the recipe ingredient name. */
    infix fun String.to(other: String) { entries[this] = other }
}

@ApiDslMarker
class InputFromScope {
    @PublishedApi internal val entries = mutableMapOf<String, String>()
    /** Reads as: API field [receiver] comes from event field [eventField]. */
    infix fun String.from(eventField: String) { entries[this] = eventField }
}

private fun KClass<*>.toEvent(): Event {
    val ctor = primaryConstructor
    val ingredients: List<Ingredient> = if (ctor != null) {
        ctor.parameters.map { Ingredient(it.name!!, it.type.javaType) }
    } else {
        memberProperties.map { Ingredient(it.name, it.returnType.javaType) }
    }
    return Event(simpleName!!, ingredients, Optional.empty())
}
