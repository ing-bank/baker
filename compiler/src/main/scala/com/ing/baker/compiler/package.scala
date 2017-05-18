package com.ing.baker

import java.lang.reflect.Method

import com.ing.baker.compiler.ReflectionHelpers._
import com.ing.baker.recipe.common.ActionType.InteractionAction
import com.ing.baker.recipe.common.{InteractionDescriptor, InteractionFailureStrategy}
import com.ing.baker.recipe.javadsl.{FiresEvent, ProvidesIngredient}
import com.ing.baker.runtime.recipe.duplicates.ActionType
import com.ing.baker.runtime.recipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.runtime.recipe.transitions.InteractionTransition
import io.kagera.api.colored.Transition

package object compiler {

  implicit class BooleanOps(bool: Boolean) {

    def toOption[T](fn: => T): Option[T] = {
      if (bool)
        Some(fn)
      else
        None
    }
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
                                 defaultFailureStrategy: com.ing.baker.recipe.common.InteractionFailureStrategy,
                                 ingredientExtractor: IngredientExtractor): InteractionTransition[Any] = {

      val interactionClass = interaction.interactionClass.asInstanceOf[Class[Any]]

      val interactionMethodName = interaction.methodName

      val method: Method = interactionClass.getDeclaredMethods
        .find(_.getName == interactionMethodName)
        .getOrElse(throw new IllegalStateException(
          s"No method named '$interactionMethodName' defined on '${interactionClass.getName}'"))

      val inputFields: Seq[(String, Class[_])] = method.getParameterNames.toSeq
        //Replace ingredient tags with overridden tags
        .map(ingredientName => interaction.overriddenIngredientNames.getOrElse(ingredientName, ingredientName))
        //Add the correct typing
        .zip(method.getParameterTypes.toSeq)

      // checks whether this interaction provides an ingredient
      val providesIngredient: Boolean = method.isAnnotationPresent(classOf[ProvidesIngredient])

      // checks whether this interaction provides an event
      val providesEvent: Boolean = method.isAnnotationPresent(classOf[FiresEvent])


      val interactionOutputName: String =
      if(providesIngredient)
      {
        if (interaction.overriddenOutputIngredientName != null && interaction.overriddenOutputIngredientName != "") {
          interaction.overriddenOutputIngredientName
        } else {
          method.getOutputName
        }
      }
      else ""

      def transformEventType(clazz: Class[_]): Class[_] =
        interaction.eventOutputTransformers
          .get(clazz)
          .fold(clazz.asInstanceOf[Class[Any]])(_.targetType.asInstanceOf[Class[Any]])


      val outputEventClasses: Seq[Class[_]] = {
        val eventClasses =
          if (providesEvent) method.getAnnotation(classOf[FiresEvent]).oneOf().toSeq else Nil

        eventClasses.map(transformEventType) //performing additional rewriting on the output events if applicable.
      }

      InteractionTransition[Any](
        method = method,
        providesIngredient = providesIngredient,
        providesEvent = providesEvent,

        inputFields = inputFields,
        interactionClass = interactionClass,
        interactionProvider = implementationProvider,
        interactionName = interaction.name,
        outputEventClasses = outputEventClasses,
        interactionOutputName = interactionOutputName,

        predefinedParameters = interaction.predefinedIngredients,
        maximumInteractionCount = interaction.maximumInteractionCount,
        //TODO create a tranformation from the recipeDsl to the CompiledRecipe
        //        failureStrategy = interaction.failureStrategy.getOrElse(defaultFailureStrategy),
        failureStrategy = com.ing.baker.runtime.recipe.duplicates.InteractionFailureStrategy.BlockInteraction,
        //TODO translate from the recipeDsl eventOutputTransformer to the runtime eventOutputTransformer
        //        eventOutputTransformers = interaction.eventOutputTransformers,
        eventOutputTransformers = Map.empty,
        actionType = if (interaction.actionType == InteractionAction) ActionType.InteractionAction else ActionType.SieveAction,
        ingredientExtractor = ingredientExtractor)
    }
  }

  implicit class TransitionOps(transitions: Seq[Transition[_, _, _]]) {

    def findTransitionsByClass: Class[_] ⇒ Option[Transition[_, _, _]] =
      clazz => transitions.findByLabel(clazz.getSimpleName)

    def findTransitionByName: String ⇒ Option[Transition[_, _, _]] =
      interactionName ⇒ transitions.findByLabel(interactionName)
  }

}
