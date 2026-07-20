package com.ing.baker.recipe.annotations

import javax.inject.Qualifier

/**
 * Annotation for an interaction to show it supports Async calls
 */
@Qualifier
@MustBeDocumented
@Retention(AnnotationRetention.RUNTIME)
@Target(AnnotationTarget.FUNCTION)
annotation class AsyncInteraction
