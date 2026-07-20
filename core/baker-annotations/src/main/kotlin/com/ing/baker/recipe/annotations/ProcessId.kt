package com.ing.baker.recipe.annotations

import javax.inject.Qualifier

/**
 * An annotation to be added to an argument of an action indicating that the process identifier should be injected
 * there.
 */
@Qualifier
@MustBeDocumented
@Retention(AnnotationRetention.RUNTIME)
@Target(AnnotationTarget.VALUE_PARAMETER)
annotation class ProcessId
