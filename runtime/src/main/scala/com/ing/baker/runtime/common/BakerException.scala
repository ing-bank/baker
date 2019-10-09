package com.ing.baker.runtime.common

sealed abstract class BakerException(message: String = "An exception occurred at Baker", cause: Throwable = null)
    extends RuntimeException(message, cause)

object BakerException {

  case class NoSuchProcessException(message: String) extends BakerException(message)

  case class ProcessDeletedException(message: String) extends BakerException(message)

  case class RecipeValidationException(message: String) extends BakerException(message)

  case class ImplementationsException(message: String) extends BakerException(message)

  case class RecipeNotFoundException(message: String) extends BakerException(message)

  case class ProcessAlreadyExistsException(message: String) extends BakerException(message)

  case class InvalidEventException(message: String) extends BakerException(message)
}
