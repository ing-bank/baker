package com.ing.baker.recipe.annotations

import javax.inject.Qualifier
import kotlin.reflect.KClass

/**
 * Annotation for an interaction to show what events can fired from this interaction
 */
@Qualifier
@MustBeDocumented
@Retention(AnnotationRetention.RUNTIME)
@Target(AnnotationTarget.FUNCTION)
annotation class FiresEvent(
    val oneOf: Array<KClass<*>>
)
