package com.ing.baker.runtime.model

import cats.effect.{Effect, Timer}
import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.BakerException.{ImplementationsException, NoSuchRecipeException, RecipeValidationException}
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.scaladsl.{RecipeAdded, RecipeInformation}

import scala.concurrent.duration

trait RecipeManager[F[_]] {

  protected def store(compiledRecipe: CompiledRecipe, timestamp: Long): F[Unit]

  protected def fetchAll: F[Map[String, RecipeRecord]]

  protected def fetch(recipeId: String): F[Option[RecipeRecord]]

  def addRecipe(compiledRecipe: CompiledRecipe, allowAddingRecipeWithoutRequiringInstances: Boolean)(implicit components: BakerComponents[F], effect: Effect[F], timer: Timer[F]): F[String] =
    for {
      implementationErrors <-
        if (allowAddingRecipeWithoutRequiringInstances) effect.pure(List.empty)
        else getImplementationErrors(compiledRecipe)
      _ <-
        if (implementationErrors.nonEmpty)
          effect.raiseError(ImplementationsException(implementationErrors.mkString(", ")))
        else if (compiledRecipe.validationErrors.nonEmpty)
          effect.raiseError(RecipeValidationException(compiledRecipe.validationErrors.mkString(", ")))
        else
          for {
            timestamp <- timer.clock.realTime(duration.MILLISECONDS)
            _ <- store(compiledRecipe, timestamp)
            _ <- components.logging.addedRecipe(compiledRecipe, timestamp)
            _ <- components.eventStream.publish(RecipeAdded(compiledRecipe.name, compiledRecipe.recipeId, timestamp, compiledRecipe))
          } yield ()
    } yield compiledRecipe.recipeId

  def getRecipe(recipeId: String)(implicit components: BakerComponents[F], effect: Effect[F]): F[RecipeInformation] =
    fetch(recipeId).flatMap[RecipeInformation] {
      case Some(r: RecipeRecord) =>
        getImplementationErrors(r.recipe).map( errors =>
          RecipeInformation(r.recipe, r.updated, errors, r.onlyInCache))
      case None =>
        effect.raiseError(NoSuchRecipeException(recipeId))
    }

  def getAllRecipes(implicit components: BakerComponents[F], effect: Effect[F]): F[Map[String, RecipeInformation]] =
    fetchAll.flatMap(_.toList
      .traverse { case (recipeId, r) =>
        getImplementationErrors(r.recipe)
          .map(errors => recipeId -> RecipeInformation(r.recipe, r.updated, errors, r.onlyInCache))
      }
      .map(_.toMap))

  private def getImplementationErrors(compiledRecipe: CompiledRecipe)(implicit components: BakerComponents[F], effect: Effect[F]): F[Set[String]] = {
    compiledRecipe.interactionTransitions.toList
      .traverse(x => components
        .interactions.incompatibilities(x)
        .map((_, x.originalInteractionName)))
      .map(_
        .filterNot(_._1.isEmpty)
        .map(x => s"No compatible implementation provided for interaction: ${x._2}: ${x._1}")
        .toSet)
  }
}
