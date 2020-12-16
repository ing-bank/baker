package com.ing.baker.runtime.model

import cats.MonadError
import cats.effect.Sync
import cats.implicits._
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FatalInteractionException
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstanceF}

trait InteractionsF[F[_]] {

  def instances: F[Seq[InteractionInstanceF[F]]]

  def findImplementation(transition: InteractionTransition)(implicit sync: Sync[F]): F[Option[InteractionInstanceF[F]]]

  def hasImplementationFor(interaction: InteractionTransition)(implicit sync: Sync[F]): F[Boolean] =
    findImplementation(interaction).map(_.nonEmpty)

  def execute(interaction: InteractionTransition, input: Seq[IngredientInstance])(implicit sync: Sync[F], effect: MonadError[F, Throwable]): F[Option[EventInstance]] =
    findImplementation(interaction)
      .flatMap {
      case Some(implementation) => implementation.execute(input)
      case None => effect.raiseError(new FatalInteractionException(s"No implementation available for interaction ${interaction.interactionName}"))
    }

  protected def compatible(transition: InteractionTransition, implementation: InteractionInstanceF[F]): Boolean = {
    val interactionNameMatches =
      transition.originalInteractionName == implementation.name
    val inputSizeMatches =
      implementation.input.size == transition.requiredIngredients.size
    val inputNamesAndTypesMatches =
      transition
        .requiredIngredients
        .forall { descriptor =>
          implementation.input.exists(_.isAssignableFrom(descriptor.`type`))
        }
    println(s"transition: $transition implementation ${implementation.name}, name: $interactionNameMatches, size $inputSizeMatches, types $inputNamesAndTypesMatches")
    interactionNameMatches && inputSizeMatches && inputNamesAndTypesMatches
  }
}

