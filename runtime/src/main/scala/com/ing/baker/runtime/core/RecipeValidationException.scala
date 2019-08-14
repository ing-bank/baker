package com.ing.baker.runtime.core

/**
  * Thrown when a (compiled) recipe with validation errors was added to Baker.
  *
  * @param reason A string with the validation errors.
  */
class RecipeValidationException(reason: String) extends BakerException(reason)
