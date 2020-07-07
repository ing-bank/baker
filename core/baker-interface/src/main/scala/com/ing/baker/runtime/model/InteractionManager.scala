package com.ing.baker.runtime.model

import cats.implicits._
import cats.effect.{ConcurrentEffect, ContextShift, IO}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance}

abstract class InteractionManager[F[_]](implicit eff: ConcurrentEffect[F], contextShift: ContextShift[IO]) {

  def addImplementation(interaction: InteractionInstance): F[Unit]

  def getImplementation(interaction: InteractionTransition): F[Option[InteractionInstance]]

  def hasImplementation(interaction: InteractionTransition): F[Boolean] =
    getImplementation(interaction).map(_.isDefined)

  def executeImplementation(interaction: InteractionTransition, input: Seq[IngredientInstance]): F[Option[EventInstance]] = {
    getImplementation(interaction).flatMap {
      case Some(implementation) => eff.liftIO(IO.fromFuture(IO(implementation.run(input))))
      case None => eff.raiseError(new IllegalStateException(s"No implementation available for interaction ${interaction.interactionName}"))
    }
  }

  protected def isCompatibleImplementation(interaction: InteractionTransition, implementation: InteractionInstance): Boolean = {
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

