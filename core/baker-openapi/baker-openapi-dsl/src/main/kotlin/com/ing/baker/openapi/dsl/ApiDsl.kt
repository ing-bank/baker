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
fun <RequestBody : Any> RecipeBuilder.api(
    operation: ApiOperation<RequestBody>,
    configure: ApiInteractionScope<RequestBody>.() -> Unit,
) {
    val scope = ApiInteractionScope(operation).apply(configure)
    addInteraction(scope.buildInteraction())
    apiInteractionConfigCollector.get()?.put(
        operation.operationName,
        ApiInteractionConfig(
            operation = operation,
            mappers = scope.configuredMappers,
            nameOverrides = scope.configuredNameOverrides,
            inputEventClass = scope.configuredInputEventClass,
            inputMapper = scope.configuredInputMapper,
        ),
    )
}

internal data class ApiInteractionConfig(
    val operation: ApiOperation<*>,
    val mappers: Map<Int, (Wirespec.Response<*>) -> Any>,
    val nameOverrides: Map<String, String>,
    /** Set when the recipe declared `inputFrom<E> { ... }`. */
    val inputEventClass: KClass<*>? = null,
    /** Reconstructed-event → wirespec body. Set when [inputEventClass] is set. */
    val inputMapper: ((Any) -> Any)? = null,
)

@ApiDslMarker
class ApiInteractionScope<RequestBody : Any> internal constructor(private val operation: ApiOperation<RequestBody>) {

    @PublishedApi
    internal val mappers = mutableMapOf<Int, (Wirespec.Response<*>) -> Any>()

    @PublishedApi
    internal val outputEventClasses = mutableSetOf<KClass<*>>()

    @PublishedApi
    internal val requiredEvents = mutableSetOf<String>()

    @PublishedApi
    internal val ingredientNameOverridesMap = mutableMapOf<String, String>()

    @PublishedApi
    internal var inputEventClass: KClass<*>? = null

    @PublishedApi
    internal var inputMapper: ((Any) -> Any)? = null

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
     * Typed input mapping — symmetric to the response side's `on<R, E>(N) { ... }`.
     * Declares that event [E] populates the API request body via the given lambda.
     * The body type is fixed by the operation (each API operation has exactly one
     * request body type), so only [E] needs to be supplied:
     *
     *   inputFrom<CreateAccountCommand> { cmd ->
     *       CreateAccountRequest(
     *           userId = cmd.customerId,
     *           profileId = cmd.profileId,
     *           ...
     *       )
     *   }
     *
     * The wirespec request DTO appears inside the lambda only — never as a
     * Baker ingredient. The runtime reconstructs an [E] instance from Baker
     * ingredients (E's primary constructor parameters), calls the mapper, and
     * lets the descriptor wrap the returned body into the operation's Request
     * envelope.
     */
    inline fun <reified E : Any> inputFrom(noinline mapper: (E) -> RequestBody) {
        requiredEvents.add(E::class.simpleName!!)
        inputEventClass = E::class
        @Suppress("UNCHECKED_CAST")
        inputMapper = { event -> mapper(event as E) }
    }

    /** Read-only view of configured mappers, useful for app-startup binding. */
    val configuredMappers: Map<Int, (Wirespec.Response<*>) -> Any> get() = mappers.toMap()

    /** Read-only view of API field → ingredient overrides. */
    val configuredNameOverrides: Map<String, String> get() = ingredientNameOverridesMap.toMap()

    /** Set when `inputFrom<E, R>(mapper)` was used. */
    val configuredInputEventClass: KClass<*>? get() = inputEventClass

    /** Set when `inputFrom<E, R>(mapper)` was used. */
    val configuredInputMapper: ((Any) -> Any)? get() = inputMapper

    internal fun buildInteraction(): Interaction {
        // When inputFrom<E, R> was declared, the interaction's required ingredients
        // are E's primary-constructor parameters (each becomes an ingredient that
        // Baker fills from the fired E event). Otherwise fall back to the API
        // descriptor's flat inputFields.
        val inputIngredients: Set<Ingredient> = inputEventClass?.let { evt ->
            evt.primaryConstructor?.parameters?.map { p ->
                Ingredient(p.name!!, p.type.javaType)
            }?.toSet()
        } ?: operation.inputFields
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

private fun KClass<*>.toEvent(): Event {
    val ctor = primaryConstructor
    val ingredients: List<Ingredient> = if (ctor != null) {
        ctor.parameters.map { Ingredient(it.name!!, it.type.javaType) }
    } else {
        memberProperties.map { Ingredient(it.name, it.returnType.javaType) }
    }
    return Event(simpleName!!, ingredients, Optional.empty())
}
