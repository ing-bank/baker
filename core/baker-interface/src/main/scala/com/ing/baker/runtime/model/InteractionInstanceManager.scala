package com.ing.baker.runtime.model

import cats.implicits._
import cats.{Functor, MonadError}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstanceF}

trait InteractionInstanceManager[F[_]] {

  def add(interaction: InteractionInstanceF[F]): F[Unit]

  def get(interaction: InteractionTransition): F[Option[InteractionInstanceF[F]]]

  def contains(interaction: InteractionTransition)(implicit effect: Functor[F]): F[Boolean] =
    get(interaction).map(_.isDefined)

  def execute(interaction: InteractionTransition, input: Seq[IngredientInstance])(implicit effect: MonadError[F, Throwable]): F[Option[EventInstance]] = {
    get(interaction).flatMap {
      case Some(implementation) => implementation.execute(input)
      case None => effect.raiseError(new IllegalStateException(s"No implementation available for interaction ${interaction.interactionName}"))
    }
  }

  protected def isCompatible(interaction: InteractionTransition, implementation: InteractionInstanceF[F]): Boolean = {
    val interactionNameMatches =
      interaction.originalInteractionName == implementation.name
    val inputSizeMatches =
      implementation.input.size == interaction.requiredIngredients.size
    val inputNamesAndTypesMatches =
      interaction
        .requiredIngredients
        .forall { descriptor =>
          implementation.input.exists(_.isAssignableFrom(descriptor.`type`))
        }
    interactionNameMatches && inputSizeMatches && inputNamesAndTypesMatches
  }
}

