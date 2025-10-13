package com.ing.baker.runtime.model

import cats.effect.{Async, Clock, Sync}
import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.BakerException.{ImplementationsException, NoSuchRecipeException, RecipeValidationException}
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.scaladsl.{RecipeAdded, RecipeInformation}
import com.typesafe.scalalogging.LazyLogging

trait RecipeManager[F[_]] extends LazyLogging {

  protected def store(compiledRecipe: CompiledRecipe, timestamp: Long): F[Unit]

  protected def fetchAll: F[Map[String, RecipeRecord]]

  protected def fetch(recipeId: String): F[Option[RecipeRecord]]

  def addRecipe(
                 compiledRecipe: CompiledRecipe,
                 suppressImplementationErrors: Boolean
               )(implicit components: BakerComponents[F], sync: Sync[F], async: Async[F]): F[String] =
    for {
      implementationErrors <-
        if (suppressImplementationErrors) sync.delay {
          logger.debug(s"Recipe implementation errors are ignored for ${compiledRecipe.name}:${compiledRecipe.recipeId}")
          List.empty[String]
        }
        else {
          logger.debug(s"Recipe ${compiledRecipe.name}:${compiledRecipe.recipeId} is validated for compatibility with interactions")
          getImplementationErrors(compiledRecipe)
        }
      _ <-
        if (implementationErrors.nonEmpty)
          Sync[F].raiseError(ImplementationsException(s"Recipe ${compiledRecipe.name}:${compiledRecipe.recipeId} has implementation errors: ${implementationErrors.mkString(", ")}"))
        else if (compiledRecipe.validationErrors.nonEmpty)
          Sync[F].raiseError(RecipeValidationException(s"Recipe ${compiledRecipe.name}:${compiledRecipe.recipeId} has validation errors: ${compiledRecipe.validationErrors.mkString(", ")}"))
        else
          for {
            timestamp <- async.pure(System.currentTimeMillis())
            _ <- store(compiledRecipe, timestamp)
            recipeAdded = RecipeAdded(compiledRecipe.name, compiledRecipe.recipeId, timestamp, compiledRecipe)
            _ <- sync.delay(components.logging.addedRecipe(recipeAdded))
            _ <- components.eventStream.publish(recipeAdded)
          } yield ()
    } yield compiledRecipe.recipeId

  def getRecipe(recipeId: String)(implicit components: BakerComponents[F], sync: Sync[F]): F[RecipeInformation] =
    fetch(recipeId).flatMap[RecipeInformation] {
      case Some(r: RecipeRecord) =>
        getImplementationErrors(r.recipe).map( errors =>
          RecipeInformation(r.recipe, r.updated, errors, r.validate, r.recipe.sensoryEvents))
      case None =>
        Sync[F].raiseError(NoSuchRecipeException(recipeId))
    }

  def getAllRecipes(implicit components: BakerComponents[F], sync: Sync[F]): F[Map[String, RecipeInformation]] =
    fetchAll
      .map(_.filter { case (_, r) => r.isActive }) // Only return active recipe records
      .flatMap(_.toList
      .traverse { case (recipeId, r) =>
        getImplementationErrors(r.recipe)
          .map(errors => recipeId -> RecipeInformation(r.recipe, r.updated, errors, r.validate, r.recipe.sensoryEvents))
      }
      .map(_.toMap))

  private def getImplementationErrors(compiledRecipe: CompiledRecipe)(implicit components: BakerComponents[F], sync: Sync[F]): F[Set[String]] = {
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
