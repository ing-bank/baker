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
    apiMappersCollector.get()?.put(operation.operationName, operation to scope.configuredMappers)
}

@ApiDslMarker
class ApiInteractionScope internal constructor(private val operation: ApiOperation) {

    @PublishedApi
    internal val mappers = mutableMapOf<Int, (Wirespec.Response<*>) -> Any>()

    @PublishedApi
    internal val outputEventClasses = mutableSetOf<KClass<*>>()

    private val requiredEvents = mutableSetOf<String>()
    private val ingredientNameOverridesMap = mutableMapOf<String, String>()
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

    fun ingredientNameOverrides(block: MutableMap<String, String>.() -> Unit) {
        ingredientNameOverridesMap.apply(block)
    }

    /** Read-only view of configured mappers, useful for app-startup binding. */
    val configuredMappers: Map<Int, (Wirespec.Response<*>) -> Any> get() = mappers.toMap()

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

private fun KClass<*>.toEvent(): Event {
    val ctor = primaryConstructor
    val ingredients: List<Ingredient> = if (ctor != null) {
        ctor.parameters.map { Ingredient(it.name!!, it.type.javaType) }
    } else {
        memberProperties.map { Ingredient(it.name, it.returnType.javaType) }
    }
    return Event(simpleName!!, ingredients, Optional.empty())
}
