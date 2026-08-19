package com.ing.baker.runtime.model

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.catseffect.{AsyncSupport, SyncSupport}
import com.ing.baker.runtime.common.BakerException.{ImplementationsException, NoSuchRecipeException, RecipeValidationException}
import com.ing.baker.runtime.common.RecipeRecord
import SyncSupport.syntax._
import com.ing.baker.runtime.scaladsl.{RecipeAdded, RecipeInformation}
import com.typesafe.scalalogging.LazyLogging

trait RecipeManager[F[_]] extends LazyLogging {

  private def traverseList[A, B](items: List[A])(f: A => F[B])(implicit sync: SyncSupport[F]): F[List[B]] =
    items.foldRight(sync.pure(List.empty[B])) { (item, acc) =>
      for {
        value <- f(item)
        values <- acc
      } yield value :: values
    }

  protected def store(compiledRecipe: CompiledRecipe, timestamp: Long): F[Unit]

  protected def fetchAll: F[Map[String, RecipeRecord]]

  protected def fetch(recipeId: String): F[Option[RecipeRecord]]

  def addRecipe(
                 compiledRecipe: CompiledRecipe,
                 suppressImplementationErrors: Boolean
               )(implicit components: BakerComponents[F], sync: SyncSupport[F], async: AsyncSupport[F]): F[String] = {
    val implementationErrorsF =
      if (suppressImplementationErrors) sync.delay {
        logger.debug(s"Recipe implementation errors are ignored for ${compiledRecipe.name}:${compiledRecipe.recipeId}")
        List.empty[String]
      }
      else {
        logger.debug(s"Recipe ${compiledRecipe.name}:${compiledRecipe.recipeId} is validated for compatibility with interactions")
        getImplementationErrors(compiledRecipe)
      }

    for {
      implementationErrors <- implementationErrorsF
      recipeId <-
        if (implementationErrors.nonEmpty)
          sync.raiseError(ImplementationsException(s"Recipe ${compiledRecipe.name}:${compiledRecipe.recipeId} has implementation errors: ${implementationErrors.mkString(", ")}"))
        else if (compiledRecipe.criticalValidationErrors.nonEmpty)
          sync.raiseError(RecipeValidationException(s"Recipe ${compiledRecipe.name}:${compiledRecipe.recipeId} has validation errors: ${compiledRecipe.validationErrors.mkString(", ")}"))
        else {
          val logWarnings =
            if (compiledRecipe.nonCriticalValidationErrors.nonEmpty)
              sync.delay(logger.warn(s"Recipe ${compiledRecipe.name}:${compiledRecipe.recipeId} has validation warnings: ${compiledRecipe.nonCriticalValidationErrors.mkString(", ")}"))
            else
              sync.unit

          for {
            _ <- logWarnings
            timestamp <- sync.delay(System.currentTimeMillis())
            _ <- store(compiledRecipe, timestamp)
            recipeAdded = RecipeAdded(compiledRecipe.name, compiledRecipe.recipeId, timestamp, compiledRecipe)
            _ <- sync.delay(components.logging.addedRecipe(recipeAdded))
            _ <- components.eventStream.publish(recipeAdded)
          } yield compiledRecipe.recipeId
        }
    } yield recipeId
  }

  def getRecipe(recipeId: String)(implicit components: BakerComponents[F], sync: SyncSupport[F]): F[RecipeInformation] =
    for {
      maybeRecipe <- fetch(recipeId)
      recipeInfo <- maybeRecipe match {
        case Some(r) =>
          for {
            errors <- getImplementationErrors(r.recipe)
          } yield RecipeInformation(r.recipe, r.updated, errors, r.validate, r.recipe.sensoryEvents)
        case None =>
          sync.raiseError(NoSuchRecipeException(recipeId))
      }
    } yield recipeInfo

  def getAllRecipes(implicit components: BakerComponents[F], sync: SyncSupport[F]): F[Map[String, RecipeInformation]] =
    for {
      activeRecipes <- sync.map(fetchAll)(_.filter { case (_, r) => r.isActive })
      recipes <- traverseList(activeRecipes.toList) { case (recipeId, r) =>
        for {
          errors <- getImplementationErrors(r.recipe)
        } yield recipeId -> RecipeInformation(r.recipe, r.updated, errors, r.validate, r.recipe.sensoryEvents)
      }
    } yield recipes.toMap

  private def getImplementationErrors(compiledRecipe: CompiledRecipe)(implicit components: BakerComponents[F], sync: SyncSupport[F]): F[Set[String]] =
    for {
      incompatibilitiesByInteraction <- traverseList(compiledRecipe.interactionTransitions.toList) { x =>
        for {
          incompatibilities <- components.interactions.incompatibilities(x)
        } yield incompatibilities -> x.originalInteractionName
      }
    } yield incompatibilitiesByInteraction
      .filterNot(_._1.isEmpty)
      .map(x => s"No compatible implementation provided for interaction: ${x._2}: ${x._1}")
      .toSet
}
