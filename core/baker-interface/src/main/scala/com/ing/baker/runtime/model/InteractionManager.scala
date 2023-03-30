package com.ing.baker.runtime.model

import cats.MonadError
import cats.effect.Sync
import cats.implicits._
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.il.{EventDescriptor, IngredientDescriptor}
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FatalInteractionException
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstanceInput}
import com.ing.baker.types.Type
import com.typesafe.config.ConfigFactory

import scala.collection.immutable.Seq

/**
  * The InteractionManager is responsible for keeping and calling al InteractionInstances.
  * The other components of Baker will not call InteractionInstances and will always go through the InteractionManager.
  * @tparam F
  */
trait InteractionManager[F[_]] {

  protected def noneIfEmpty(str: String) = if (str.isEmpty) None else Some(str)

  /**
    * If this is set to true it will also allow fur supersets of the output types to be given by the implementations
    * This can be helpful in case an ENUM type or similar is extended upon and you know these new values will not be given.
    * If this new value is given from the implementation this will result in te runtime error and a technical failure of the interaction.
    */
  def allowSupersetForOutputTypes: Boolean = AllowSupersetForOutputTypes
  private lazy val AllowSupersetForOutputTypes: Boolean =
    ConfigFactory.load().getBoolean("baker.interactions.allow-superset-for-output-types")

  def listAll: F[List[InteractionInstance[F]]]

  def recipeAdded(recipeRecord: RecipeRecord)(implicit sync: Sync[F]): F[Unit] = Sync[F].unit

  def findFor(transition: InteractionTransition)(implicit sync: Sync[F]): F[Option[InteractionInstance[F]]] =
    listAll.flatMap(all => sync.delay(all.find(compatible(transition, _))))

  def existsFor(interaction: InteractionTransition)(implicit sync: Sync[F]): F[Boolean] = findFor(interaction).map(_.nonEmpty)

  def execute(interaction: InteractionTransition, input: Seq[IngredientInstance], metadata: Option[Map[String, String]])(implicit sync: Sync[F], effect: MonadError[F, Throwable]): F[Option[EventInstance]] =
    findFor(interaction)
      .flatMap {
        case Some(implementation) => implementation.execute(input, metadata.getOrElse(Map()))
        case None => effect.raiseError(new FatalInteractionException(s"No implementation available for interaction ${interaction.interactionName}"))
      }

  private def interactionNameMatches(transition: InteractionTransition, implementation: InteractionInstance[F]): Boolean =
    transition.originalInteractionName == implementation.name || transition.interactionName == implementation.name

  private def inputSizeMatches(transition: InteractionTransition, implementation: InteractionInstance[F]): Boolean =
    implementation.input.size == transition.requiredIngredients.size

  private def inputNamesAndTypesMatches(transition: InteractionTransition, implementation: InteractionInstance[F]): Boolean =
    transition.requiredIngredients.forall(transitionIngredient => {
      implementation.input.exists(implementationIngredient => {
        //We cannot use the name of the interaction input since we do not store the original input name.
        //This means it will not bind on renamed ingredients.
        implementationIngredient.`type`.isAssignableFrom(transitionIngredient.`type`)
      }
      )
    })

  private def outputEventNamesAndTypesMatches(transition: InteractionTransition, implementation: InteractionInstance[F]): Boolean = {
    if (implementation.output.isDefined)
    //For the output it is allowed
      implementation.output.get.size <= transition.originalEvents.size &&
        implementation.output.exists(doesOutputMatch(_, transition.originalEvents))
    else true //If the implementation output is not defined the output validation should be not done
  }

  protected def compatible(transition: InteractionTransition, implementation: InteractionInstance[F]): Boolean = {
    interactionNameMatches(transition, implementation) &&
      inputSizeMatches(transition, implementation) &&
      inputNamesAndTypesMatches(transition, implementation) &&
      outputEventNamesAndTypesMatches(transition, implementation)
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
          (transitionIngredient.`type`.isAssignableFrom(implementationIngredient._2) ||
            allowSupersetForOutputTypes && implementationIngredient._2.isAssignableFrom(transitionIngredient.`type`))
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
                                         transitionInputTypesMissing: Seq[IngredientDescriptor],
                                         implementationInputTypesExtra: Seq[InteractionInstanceInput]
                                       ) extends InteractionIncompatible {
    override def toString: String =
      s"$interactionName input types mismatch: transition expects $transitionInputTypesMissing, not provided by implementation, implementation provides extra: $implementationInputTypesExtra"
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
    if (!inputSizeMatches(transition, implementation))
      Some(InteractionMatchInputSizeFailed(transition.interactionName, transition.requiredIngredients.size, implementation.input.size))
    else if (!inputNamesAndTypesMatches(transition, implementation)) {
      val missingTypes = transition.requiredIngredients.flatMap(i => {
        if (implementation.input.map(_.`type`).exists(_.isAssignableFrom(i.`type`))) None else Some(i)
      })
      val extraTypes = implementation.input.flatMap(i => {
        if (transition.requiredIngredients.map(_.`type`).exists(_.isAssignableFrom(i.`type`))) None else Some(i)
      })
      Some(InteractionMatchInputFailed(implementation.name, missingTypes, extraTypes))
    }
    else if (!outputEventNamesAndTypesMatches(transition, implementation))
      Some(InteractionMatchOutputNotFound(transition.interactionName, transition.originalEvents))
    else
      Some(UnknownReason("Unknown reason"))
}

