package com.ing.baker.runtime.model

import cats.MonadError
import cats.effect.Sync
import cats.implicits._
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FatalInteractionException
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstanceF}
import com.ing.baker.types.Type

trait InteractionsF[F[_]] {

  def listAll: F[List[InteractionInstanceF[F]]]

  def findFor(transition: InteractionTransition)(implicit sync: Sync[F]): F[Option[InteractionInstanceF[F]]] =
    listAll.flatMap(all => sync.delay(all.find(compatible(transition, _))))

  def existsFor(interaction: InteractionTransition)(implicit sync: Sync[F]): F[Boolean] = findFor(interaction).map(_.nonEmpty)

  def execute(interaction: InteractionTransition, input: Seq[IngredientInstance])(implicit sync: Sync[F], effect: MonadError[F, Throwable]): F[Option[EventInstance]] =
    findFor(interaction)
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
    interactionNameMatches && inputSizeMatches && inputNamesAndTypesMatches
  }


  sealed trait InteractionIncompatible
  case object NameNotFound extends InteractionIncompatible
  case class InteractionMatchInputSizeFailed(
                                              interactionName: String,
                                              transitionArgsSize: Int,
                                              implementationArgsSize: Int
                                            ) extends InteractionIncompatible {
    override def toString: String =
      s"($interactionName input size differs: transition expects $transitionArgsSize, implementation provides $implementationArgsSize)"
  }

  case class InteractionMatchTypeFailed(
                                         interactionName: String,
                                         transitionInputTypesMissing: Seq[Type]
                                       ) extends InteractionIncompatible {
    override def toString: String =
      s"$interactionName input types mismatch: transition expects $transitionInputTypesMissing, not provided by implementation"
  }

  def incompatibilities(transition: InteractionTransition)(implicit sync: Sync[F]): F[Seq[InteractionIncompatible]] = for {
    all <- listAll
  } yield {
    if (all.exists(compatible(transition, _)))
      Seq.empty
    else {
      all.filter(_.name == transition.originalInteractionName) match {
        case Nil => Seq(NameNotFound)
        case sameName => sameName.flatMap(incompatibilityReason(transition, _))
      }
    }
  }

  def incompatibilityReason(transition: InteractionTransition, implementation: InteractionInstanceF[F]): Option[InteractionIncompatible] =
    if (implementation.input.size != transition.requiredIngredients.size)
      Some(InteractionMatchInputSizeFailed(implementation.name, transition.requiredIngredients.size, implementation.input.size))
    else {
      val missingTypes = transition.requiredIngredients.flatMap(i => {
        if (implementation.input.exists(_.isAssignableFrom(i.`type`))) None else Some(i.`type`)
      })
      if (missingTypes.nonEmpty)
        Some(InteractionMatchTypeFailed(implementation.name, missingTypes))
      else
        None
    }
}

