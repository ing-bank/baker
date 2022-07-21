package com.ing.baker.runtime.common

import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success, Try}

sealed abstract class BakerException(val message: String = "An exception occurred at Baker",
                                     val `enum`: Int,
                                     val cause: Throwable = null,
                                    // If the exception is created in a json decoder, instead of at the original place it
                                    // is thrown, disable the stack trace, as will point to the decoder, which is incorrect/misleading.
                                     disableStackTrace: Boolean = false
                                    )
    extends RuntimeException(message, cause, false, !disableStackTrace)

object BakerException {

  // TODO this has to be renamed to NoSuchRecipeInstanceException
  case class NoSuchProcessException(recipeInstanceId: String, disableStackTrace: Boolean = false)
    extends BakerException(s"Recipe instance $recipeInstanceId does not exist in the index", 1, disableStackTrace = disableStackTrace)

  // TODO this has to be renamed to RecipeInstanceDeletedException
  case class ProcessDeletedException(recipeInstanceId: String, disableStackTrace: Boolean = false)
    extends BakerException(s"Recipe instance $recipeInstanceId is deleted", 2, disableStackTrace = disableStackTrace)

  case class RecipeValidationException(validationErrors: String, disableStackTrace: Boolean = false)
    extends BakerException(validationErrors, 3, disableStackTrace = disableStackTrace)

  case class ImplementationsException(implementationErrors: String, disableStackTrace: Boolean = false)
    extends BakerException(implementationErrors, 4, disableStackTrace = disableStackTrace)

  case class NoSuchRecipeException(recipeId: String, disableStackTrace: Boolean = false)
    extends BakerException(s"No recipe found for recipe with id: $recipeId", 5, disableStackTrace = disableStackTrace)

  // TODO this has to be renamed to RecipeInstanceAlreadyExistsException
  case class ProcessAlreadyExistsException(recipeInstanceId: String, disableStackTrace: Boolean = false)
    extends BakerException(s"Process '$recipeInstanceId' already exists.", 6, disableStackTrace = disableStackTrace)

  case class IllegalEventException(reason: String, disableStackTrace: Boolean = false)
    extends BakerException(reason, 7, disableStackTrace = disableStackTrace)

  case class SingleInteractionExecutionFailedException(reason: String, disableStackTrace: Boolean = false)
    extends BakerException(reason, 8, disableStackTrace = disableStackTrace)

  case class UnexpectedException(errorId: String, disableStackTrace: Boolean = false)
    extends BakerException(s"Unexpected exception happened. Please look for '$errorId' in the logs.", 9, disableStackTrace = disableStackTrace)

  case class TimeoutException(operationName: String, disableStackTrace: Boolean = false)
    extends BakerException(s"'$operationName' duration exceeded timeout", 10, disableStackTrace = disableStackTrace)

  // To be used if a serialized baker exception cannot be deserialized into a specific exception.
  // This can happen when a bakery-state version is higher and contains more exceptions than the bakery-client.
  case class UnknownBakerException(underlyingErrorMessage: String, disableStackTrace: Boolean = false)
    extends BakerException(underlyingErrorMessage, 11, disableStackTrace = disableStackTrace)

  def encode(bakerException: BakerException): (String, Int) =
    bakerException match {
      case e @ NoSuchProcessException(recipeInstanceId, _) => (recipeInstanceId, e.`enum`)
      case e @ ProcessDeletedException(recipeInstanceId, _) => (recipeInstanceId, e.`enum`)
      case e @ RecipeValidationException(validationErrors, _) => (validationErrors, e.`enum`)
      case e @ ImplementationsException(implementationErrors, _) => (implementationErrors, e.`enum`)
      case e @ NoSuchRecipeException(recipeId, _) => (recipeId, e.`enum`)
      case e @ ProcessAlreadyExistsException(recipeInstanceId, _) => (recipeInstanceId, e.`enum`)
      case e @ IllegalEventException(reason, _) => (reason, e.`enum`)
      case e @ SingleInteractionExecutionFailedException(reason, _) => (reason, e.`enum`)
      case e @ UnexpectedException(errorId, _) => (errorId, e.`enum`)
      case e @ TimeoutException(operationName, _) => (operationName, e.`enum`)
      case e @ UnknownBakerException(underlyingErrorMessage, _) => (underlyingErrorMessage, e.`enum`)
      case be if be.isInstanceOf[BakerException] => (be.message, be.`enum`)
    }

  def decode(message: String, `enum`: Int): Try[BakerException] =
    `enum` match {
      case 1 => Success(NoSuchProcessException(message, disableStackTrace = true))
      case 2 => Success(ProcessDeletedException(message, disableStackTrace = true))
      case 3 => Success(RecipeValidationException(message, disableStackTrace = true))
      case 4 => Success(ImplementationsException(message, disableStackTrace = true))
      case 5 => Success(NoSuchRecipeException(message, disableStackTrace = true))
      case 6 => Success(ProcessAlreadyExistsException(message, disableStackTrace = true))
      case 7 => Success(IllegalEventException(message, disableStackTrace = true))
      case 8 => Success(SingleInteractionExecutionFailedException(message, disableStackTrace = true))
      case 9 => Success(UnexpectedException(message, disableStackTrace = true))
      case 10 => Success(TimeoutException(message, disableStackTrace = true))
      case 11 => Success(UnknownBakerException(message, disableStackTrace = true))
      case _ => Failure(new IllegalArgumentException(s"No BakerException with enum flag $enum"))
    }

  def decodeOrUnknownException(message: String, `enum`: Int): BakerException =
    decode(message, `enum`).getOrElse(UnknownBakerException(message, disableStackTrace = true))

  implicit class TimeoutExceptionHelper[A](val f : Future[A]) {
    def javaTimeoutToBakerTimeout(operationName: String)(implicit executor: ExecutionContext) : Future[A] =
      f.recoverWith {
        case _ : java.util.concurrent.TimeoutException => Future.failed(BakerException.TimeoutException(operationName))
      }
  }
}
