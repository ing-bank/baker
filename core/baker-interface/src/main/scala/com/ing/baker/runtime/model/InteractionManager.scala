package com.ing.baker.runtime.model

import cats.MonadError
import cats.effect.Sync
import cats.implicits._
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.il.{EventDescriptor, IngredientDescriptor}
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FatalInteractionException
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance}
import com.ing.baker.types.Type


/**
  * The InteractionManager is responsible for keeping and calling al InteractionInstances.
  * The other components of Baker will not call InteractionInstances and will always go through the InteractionManager.
  * @tparam F
  */
trait InteractionManager[F[_]] {


  def listAll: F[List[InteractionInstance[F]]]

  def findFor(transition: InteractionTransition)(implicit sync: Sync[F]): F[Option[InteractionInstance[F]]] =
    listAll.flatMap(all => sync.delay(all.find(compatible(transition, _))))

  def existsFor(interaction: InteractionTransition)(implicit sync: Sync[F]): F[Boolean] = findFor(interaction).map(_.nonEmpty)

  def execute(interaction: InteractionTransition, input: Seq[IngredientInstance])(implicit sync: Sync[F], effect: MonadError[F, Throwable]): F[Option[EventInstance]] =
    findFor(interaction)
      .flatMap {
        case Some(implementation) => implementation.execute(input)
        case None => effect.raiseError(new FatalInteractionException(s"No implementation available for interaction ${interaction.interactionName}"))
      }

  protected def compatible(transition: InteractionTransition, implementation: InteractionInstance[F]): Boolean = {
    val interactionNameMatches: Boolean =
      transition.originalInteractionName == implementation.name
    val inputSizeMatches: Boolean =
      implementation.input.size == transition.requiredIngredients.size
    val inputNamesAndTypesMatches: Boolean =
      implementation.input.forall(ingredient => {
        transition.requiredIngredients.exists(descriptor => {
          //We cannot use the name of the interaction input since we do not store the original input name.
          //This means it will not bind on renamed ingredients.
          descriptor.`type`.isAssignableFrom(ingredient.`type`)
        }
      )})

    val outputEventNamesAndTypesMatches: Boolean =
      if (implementation.output.isDefined)
        //For the output it is allowed
        implementation.output.get.size <= transition.originalEvents.size &&
        implementation.output.exists(doesOutputMatch(_, transition.originalEvents))
      else true //If the implementation output is not defined the output validation should be not done

    interactionNameMatches && inputSizeMatches && inputNamesAndTypesMatches && outputEventNamesAndTypesMatches
  }

  private def doesOutputMatch(implementationOutput: Map[String, Map[String, Type]], transitionOutput: Seq[EventDescriptor]): Boolean = {
    implementationOutput
      .forall { implEvent =>
        transitionOutput.exists(output =>
          output.name == implEvent._1 &&
          doesEventIngredientExists(implEvent._2, output.ingredients))
      }
  }

  private def doesEventIngredientExists(implementationIngredients: Map[String, Type], transitionIngredients: Seq[IngredientDescriptor]): Boolean = {
    transitionIngredients.forall(transitionIngredient =>
      implementationIngredients.exists(implementationIngredient =>
        transitionIngredient.name == implementationIngredient._1 &&
        transitionIngredient.`type`.isAssignableFrom(implementationIngredient._2)
      ))
  }


  sealed trait InteractionIncompatible
  case object NameNotFound extends InteractionIncompatible
  case class InteractionMatchInputSizeFailed(
                                              interactionName: String,
                                              transitionArgsSize: Int,
                                              implementationArgsSize: Int
                                            ) extends InteractionIncompatible {
    override def toString: String =
      s"$interactionName input size differs: transition expects $transitionArgsSize, implementation provides $implementationArgsSize"
  }

  case class InteractionMatchInputFailed(
                                         interactionName: String,
                                         transitionInputTypesMissing: Seq[IngredientDescriptor]
                                       ) extends InteractionIncompatible {
    override def toString: String =
      s"$interactionName input types mismatch: transition expects $transitionInputTypesMissing, not provided by implementation"
  }

  case class InteractionMatchOutputSizeFailed(interactionName: String,
                                              transitionArgsSize: Int,
                                              implementationArgsSize: Int) extends InteractionIncompatible {
    override def toString: String =
      s"$interactionName output size differs: transition expects $transitionArgsSize, implementation provides $implementationArgsSize"
  }

  case class InteractionMatchOutputNotFound(interactionName: String,
                                            eventDescriptors: Seq[EventDescriptor]) extends InteractionIncompatible {
    override def toString: String =
      s"$interactionName ouput mismatch: transition expects $eventDescriptors, not provided by implementation"
  }

  case class UnknownReason(interactionName: String) extends InteractionIncompatible {
    override def toString: String =
      s"$interactionName: unknown reason for no interaction matched"
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

  def incompatibilityReason(transition: InteractionTransition, implementation: InteractionInstance[F]): Option[InteractionIncompatible] =
    if (implementation.input.size != transition.requiredIngredients.size)
      Some(InteractionMatchInputSizeFailed(transition.interactionName, transition.requiredIngredients.size, implementation.input.size))
    else if(implementation.output.isDefined && implementation.output.get.size > transition.originalEvents.size)
      Some(InteractionMatchOutputSizeFailed(transition.interactionName, transition.originalEvents.size, implementation.output.get.size))
    else if (implementation.output.isDefined && !implementation.output.exists(doesOutputMatch(_, transition.originalEvents)))
      Some(InteractionMatchOutputNotFound(transition.interactionName, transition.originalEvents))
    else {
      val missingTypes = transition.requiredIngredients.flatMap(i => {
        if (implementation.input.map(_.`type`).exists(_.isAssignableFrom(i.`type`))) None else Some(i)
      })
      if (missingTypes.nonEmpty)
        Some(InteractionMatchInputFailed(implementation.name, missingTypes))
      else
        Some(UnknownReason("Unknown reason"))
    }
}

