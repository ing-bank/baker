package com.ing.baker.runtime.common

sealed abstract class BakerException(message: String = "An exception occurred at Baker", cause: Throwable = null)
    extends RuntimeException(message, cause)

object BakerException {

  class NoSuchProcessException(message: String) extends BakerException(message)

  class ProcessDeletedException(message: String) extends BakerException(message)

  class RecipeValidationException(message: String) extends BakerException(message)

  class ImplementationsException(message: String) extends BakerException(message)
}
