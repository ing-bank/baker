package com.ing.baker.runtime.model

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.BakerException.{ImplementationsException, NoSuchRecipeException, RecipeValidationException}
import com.ing.baker.runtime.common.{RecipeRecord, SyncSupport}
import com.ing.baker.runtime.scaladsl.{RecipeAdded, RecipeInformation}
import com.typesafe.scalalogging.LazyLogging

trait RecipeManager[F[_]] extends LazyLogging {

  private def traverseList[A, B](items: List[A])(f: A => F[B])(implicit sync: SyncSupport[F]): F[List[B]] =
    items.foldRight(sync.pure(List.empty[B])) { (item, acc) =>
      sync.flatMap(f(item))(value => sync.map(acc)(value :: _))
    }

  protected def store(compiledRecipe: CompiledRecipe, timestamp: Long): F[Unit]

  protected def fetchAll: F[Map[String, RecipeRecord]]

  protected def fetch(recipeId: String): F[Option[RecipeRecord]]

  def addRecipe(
                 compiledRecipe: CompiledRecipe,
                 suppressImplementationErrors: Boolean
               )(implicit components: BakerComponents[F], sync: SyncSupport[F]): F[String] = {
    val implementationErrorsF =
      if (suppressImplementationErrors) sync.delay {
        logger.debug(s"Recipe implementation errors are ignored for ${compiledRecipe.name}:${compiledRecipe.recipeId}")
        List.empty[String]
      }
      else {
        logger.debug(s"Recipe ${compiledRecipe.name}:${compiledRecipe.recipeId} is validated for compatibility with interactions")
        getImplementationErrors(compiledRecipe)
      }

    sync.flatMap(implementationErrorsF) { implementationErrors =>
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

        sync.flatMap(logWarnings) { _ =>
          sync.flatMap(sync.delay(System.currentTimeMillis())) { timestamp =>
            sync.flatMap(store(compiledRecipe, timestamp)) { _ =>
              val recipeAdded = RecipeAdded(compiledRecipe.name, compiledRecipe.recipeId, timestamp, compiledRecipe)
              sync.flatMap(sync.delay(components.logging.addedRecipe(recipeAdded))) { _ =>
                sync.map(sync.delay(components.eventStream.publish(recipeAdded)))(_ => compiledRecipe.recipeId)
              }
            }
          }
        }
      }
    }
  }

  def getRecipe(recipeId: String)(implicit components: BakerComponents[F], sync: SyncSupport[F]): F[RecipeInformation] =
    sync.flatMap(fetch(recipeId)) {
      case Some(r: RecipeRecord) =>
        sync.map(getImplementationErrors(r.recipe))(errors =>
          RecipeInformation(r.recipe, r.updated, errors, r.validate, r.recipe.sensoryEvents))
      case None =>
        sync.raiseError(NoSuchRecipeException(recipeId))
    }

  def getAllRecipes(implicit components: BakerComponents[F], sync: SyncSupport[F]): F[Map[String, RecipeInformation]] =
    sync.flatMap(sync.map(fetchAll)(_.filter { case (_, r) => r.isActive })) { activeRecipes =>
      sync.map(traverseList(activeRecipes.toList) { case (recipeId, r) =>
        sync.map(getImplementationErrors(r.recipe))(errors =>
          recipeId -> RecipeInformation(r.recipe, r.updated, errors, r.validate, r.recipe.sensoryEvents))
      })(_.toMap)
    }

  private def getImplementationErrors(compiledRecipe: CompiledRecipe)(implicit components: BakerComponents[F], sync: SyncSupport[F]): F[Set[String]] =
    sync.map(
      traverseList(compiledRecipe.interactionTransitions.toList) { x =>
        sync.map(components.interactions.incompatibilities(x))(incompatibilities =>
          incompatibilities -> x.originalInteractionName)
      }
    )(_.filterNot(_._1.isEmpty)
      .map(x => s"No compatible implementation provided for interaction: ${x._2}: ${x._1}")
      .toSet)
}
