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

import scala.concurrent.duration.Duration
import scala.reflect.ClassTag

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

      implicit def transformFailureStrategy(recipeStrategy: com.ing.baker.recipe.common.InteractionFailureStrategy): com.ing.baker.runtime.recipe.duplicates.InteractionFailureStrategy = {
        recipeStrategy match {
          case com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff(initialTimeout: Duration, backoffFactor: Double, maximumRetries: Int) => com.ing.baker.runtime.recipe.duplicates.InteractionFailureStrategy.RetryWithIncrementalBackoff(initialTimeout, backoffFactor, maximumRetries)
          case com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction => com.ing.baker.runtime.recipe.duplicates.InteractionFailureStrategy.BlockInteraction
          case _ => com.ing.baker.runtime.recipe.duplicates.InteractionFailureStrategy.BlockInteraction
        }
      }

      def transformEventOutputTransformers[A: ClassTag, B: ClassTag](recipeEventOutputTransformer: com.ing.baker.recipe.common.EventOutputTransformer[A, B]) : com.ing.baker.runtime.recipe.duplicates.EventOutputTransformer[A, B] = {
         com.ing.baker.runtime.recipe.duplicates.EventOutputTransformer[A, B](recipeEventOutputTransformer.fn)
      }

      implicit def transformEventOutputTransformersMap(eventOutputTransformersMap : Map[Class[_], com.ing.baker.recipe.common.EventOutputTransformer[_, _]]) : Map[Class[_], com.ing.baker.runtime.recipe.duplicates.EventOutputTransformer[_, _]] = {
        eventOutputTransformersMap.map(e => (e._1, transformEventOutputTransformers(e._2))).toMap
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
        failureStrategy = interaction.failureStrategy.getOrElse[com.ing.baker.recipe.common.InteractionFailureStrategy](defaultFailureStrategy),
        eventOutputTransformers = interaction.eventOutputTransformers,
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
