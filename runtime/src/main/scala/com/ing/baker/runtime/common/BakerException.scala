package com.ing.baker.runtime.common

import scala.util.{Failure, Success, Try}

sealed abstract class BakerException(val message: String = "An exception occurred at Baker", val enum: Int, val cause: Throwable = null)
    extends RuntimeException(message, cause)

object BakerException {

  // TODO this has to be renamed to NoSuchRecipeInstanceException
  case class NoSuchProcessException(recipeInstanceId: String)
    extends BakerException(s"Recipe instance $recipeInstanceId does not exist in the index", 1)

  // TODO this has to be renamed to RecipeInstanceDeletedException
  case class ProcessDeletedException(recipeInstanceId: String)
    extends BakerException(s"Recipe instance $recipeInstanceId is deleted", 2)

  case class RecipeValidationException(validationErrors: String)
    extends BakerException(validationErrors, 3)

  case class ImplementationsException(implementationErrors: String)
    extends BakerException(implementationErrors, 4)

  case class NoSuchRecipeException(recipeId: String)
    extends BakerException(s"No recipe found for recipe with id: $recipeId", 5)

  // TODO this has to be renamed to RecipeInstanceAlreadyExistsException
  case class ProcessAlreadyExistsException(recipeInstanceId: String)
    extends BakerException(s"Process '$recipeInstanceId' already exists.", 6)

  case class IllegalEventException(reason: String)
    extends BakerException(reason, 7)

  def encode(bakerException: BakerException): (String, Int) =
    bakerException match {
      case e @ NoSuchProcessException(recipeInstanceId) => (recipeInstanceId, e.enum)
      case e @ ProcessDeletedException(recipeInstanceId) => (recipeInstanceId, e.enum)
      case e @ RecipeValidationException(validationErrors) => (validationErrors, e.enum)
      case e @ ImplementationsException(implementationErrors) => (implementationErrors, e.enum)
      case e @ NoSuchRecipeException(recipeId) => (recipeId, e.enum)
      case e @ ProcessAlreadyExistsException(recipeInstanceId) => (recipeInstanceId, e.enum)
      case e @ IllegalEventException(reason) => (reason, e.enum)
    }

  def decode(message: String, enum: Int): Try[BakerException] =
    enum match {
      case 1 => Success(NoSuchProcessException(message))
      case 2 => Success(ProcessDeletedException(message))
      case 3 => Success(RecipeValidationException(message))
      case 4 => Success(ImplementationsException(message))
      case 5 => Success(NoSuchRecipeException(message))
      case 6 => Success(ProcessAlreadyExistsException(message))
      case 7 => Success(IllegalEventException(message))
      case _ => Failure(new IllegalArgumentException(s"No BakerException with enum flag $enum"))
    }
}
