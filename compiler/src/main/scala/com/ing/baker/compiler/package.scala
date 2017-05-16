package com.ing.baker

import com.ing.baker.compiler.transitions.InteractionTransition
import com.ing.baker.recipe.common.ActionType.{InteractionAction, SieveAction}
import com.ing.baker.recipe.common.{InteractionDescriptor, InteractionFailureStrategy}
import io.kagera.api.colored.{Place, Transition}

package object compiler {

  val limitPrefix           = "limit:"
  val preconditionPrefix    = "precondition:"
  val orPreconditionPrefix  = "orPrecondition:"
  val interactionEvent      = "result:"
  val multiTransitionPrefix = "multi:"
  val processIdName         = "$ProcessID$"
  val missingEvent          = "missing:"
  val emptyEventIngredient     = "EEI:"

  implicit class BooleanOps(bool: Boolean) {

    def toOption[T](fn: => T): Option[T] = {
      if (bool)
        Some(fn)
      else
        None
    }
  }

  implicit class PlaceAdditions(place: Place[_]) {
    def isIngredient: Boolean =
      !isInteractionEventOutput && !isEventPrecondition && !isFiringLimiter && !isIntermediate
    def isInteractionEventOutput: Boolean = place.label.startsWith(interactionEvent)
    def isFiringLimiter: Boolean          = place.label.startsWith(limitPrefix)
    def isEventPrecondition: Boolean      = place.label.startsWith(preconditionPrefix)
    def isOrEventPrecondition: Boolean    = place.label.startsWith(orPreconditionPrefix)
    def isIntermediate: Boolean           = place.label.startsWith(multiTransitionPrefix)
    def isEmptyEventIngredient: Boolean   = place.label.startsWith(emptyEventIngredient)
  }

  implicit class TransitionAdditions(transition: Transition[_, _, _]) {
    def isParallelizationTransition: Boolean = transition.label.startsWith(multiTransitionPrefix)
    def isInteraction: Boolean = PartialFunction.cond(transition) {
      case t: InteractionTransition[_] => t.actionType == InteractionAction
    }
    def isSieve: Boolean = PartialFunction.cond(transition) {
      case t: InteractionTransition[_] => t.actionType == SieveAction
    }
    def isEventMissing: Boolean =
      !transition
        .isInstanceOf[InteractionTransition[_]] && transition.label.startsWith(missingEvent)

    def isEvent: Boolean =
      !(transition.isInstanceOf[InteractionTransition[_]] || transition.label.contains(":"))
  }

  implicit class InteractionOps(interaction: InteractionDescriptor[_]) {

    def toInteractionTransition(implementations: Map[Class[_], () => AnyRef],
                                defaultFailureStrategy: InteractionFailureStrategy,
                                ingredientExtractor: IngredientExtractor): (InteractionTransition[_], Seq[String]) = {

      val validationErrors = scala.collection.mutable.MutableList.empty[String]

      // validate that an implementation is provided for the interaction
      if (!implementations.isDefinedAt(interaction.interactionClass))
        validationErrors += s"No implementation provided for interaction: ${interaction.interactionClass}"

      val implementationProvider = implementations.lift(interaction.interactionClass).getOrElse(() => null)
      val interactionTransition = interactionTransitionOf(interaction, implementationProvider, defaultFailureStrategy, ingredientExtractor)

      (interactionTransition, validationErrors)
    }

    def interactionTransitionOf(
        interaction: InteractionDescriptor[_],
        implementationProvider: () => AnyRef,
        defaultFailureStrategy: InteractionFailureStrategy,
        ingredientExtractor: IngredientExtractor): InteractionTransition[Any] =

      InteractionTransition[Any](
        interactionClass = interaction.interactionClass.asInstanceOf[Class[Any]],
        interactionProvider = implementationProvider,
        interactionMethod = interaction.methodName,
        interactionName = interaction.name,
        predefinedParameters = interaction.predefinedIngredients,
        overriddenIngredientNames = interaction.overriddenIngredientNames,
        maximumInteractionCount = interaction.maximumInteractionCount,
        overriddenOutputIngredientName = interaction.overriddenOutputIngredientName,
        failureStrategy = interaction.failureStrategy.getOrElse(defaultFailureStrategy),
        eventOutputTransformers = interaction.eventOutputTransformers,
        actionType = interaction.actionType,
        ingredientExtractor = ingredientExtractor)
  }

  implicit class TransitionOps(transitions: Seq[Transition[_, _, _]]) {

    def findTransitionsByClass: Class[_] ⇒ Option[Transition[_, _, _]] =
      clazz => transitions.findByLabel(clazz.getSimpleName)

    def findTransitionByName: String ⇒ Option[Transition[_, _, _]] =
      interactionName ⇒ transitions.findByLabel(interactionName)
  }

}
