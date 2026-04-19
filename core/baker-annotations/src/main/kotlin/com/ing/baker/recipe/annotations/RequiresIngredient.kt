package com.ing.baker.recipe.annotations

import javax.inject.Qualifier

/**
 * An annotation to be added to an argument of an interaction to show what ingredient should be used here.
 */
@Qualifier
@MustBeDocumented
@Retention(AnnotationRetention.RUNTIME)
@Target(AnnotationTarget.VALUE_PARAMETER)
annotation class RequiresIngredient(
    val value: String = ""
)
