package com.ing.baker

import java.lang.reflect.Method

import com.ing.baker.compiledRecipe.ActionType.{InteractionAction, SieveAction}
import com.ing.baker.compiledRecipe.annotations.FiresEvent
import com.ing.baker.compiledRecipe.duplicates.ReflectionHelpers._
import com.ing.baker.compiledRecipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.compiledRecipe.petrinet.{InteractionTransition, ProvidesType}
import com.ing.baker.compiledRecipe.petrinet.ProvidesType.{ProvidesEvent, ProvidesIngredient, ProvidesNothing}
import com.ing.baker.compiledRecipe.petrinet.ProvidesType
import com.ing.baker.compiledRecipe.{ActionType, EventOutputTransformer, InteractionFailureStrategy, annotations}
import com.ing.baker.recipe.common.InteractionDescriptor
import io.kagera.api._
import io.kagera.dsl.colored._

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
                                defaultFailureStrategy: com.ing.baker.recipe.common.InteractionFailureStrategy,
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
                                 interactionDescriptor: InteractionDescriptor[_],
                                 implementationProvider: () => AnyRef,
                                 defaultFailureStrategy: com.ing.baker.recipe.common.InteractionFailureStrategy,
                                 ingredientExtractor: IngredientExtractor): InteractionTransition[Any] = {

      val interactionClass = interactionDescriptor.interactionClass.asInstanceOf[Class[Any]]

      val interactionMethodName = interactionDescriptor.methodName

      val method: Method = interactionClass.getDeclaredMethods
        .find(_.getName == interactionMethodName)
        .getOrElse(throw new IllegalStateException(
          s"No method named '$interactionMethodName' defined on '${interactionClass.getName}'"))

      val inputFields: Seq[(String, Class[_])] = method.getParameterNames.toSeq
        //Replace ingredient tags with overridden tags
        .map(ingredientName => interactionDescriptor.overriddenIngredientNames.getOrElse(ingredientName, ingredientName))
        //Add the correct typing
        .zip(method.getParameterTypes.toSeq)

      def transformEventType(clazz: Class[_]): Class[_] =
        interactionDescriptor.eventOutputTransformers
          .get(clazz)
          .fold(clazz.asInstanceOf[Class[Any]])(_.targetType.asInstanceOf[Class[Any]])

      val returnType = if (method.isAsynchronous) method.getFirstTypeParameter else method.getReturnType

      val providesType: ProvidesType =
        //ProvidesIngredient
        if(method.isAnnotationPresent(classOf[annotations.ProvidesIngredient]))
        {
          val interactionOutputName: String =
            if (interactionDescriptor.overriddenOutputIngredientName != null && interactionDescriptor.overriddenOutputIngredientName != "") {
              interactionDescriptor.overriddenOutputIngredientName
            } else {
              method.getAnnotation(classOf[annotations.ProvidesIngredient]).value()
            }
          ProvidesIngredient(interactionOutputName -> returnType, returnType)
        }
        //ProvidesEvent
        else if(method.isAnnotationPresent(classOf[annotations.FiresEvent])) {
          val outputType = transformEventType(returnType)
          val outputEventClasses: Seq[Class[_]] = {
            val eventClasses = method.getAnnotation(classOf[annotations.FiresEvent]).oneOf().toSeq
            eventClasses.map(transformEventType) //performing additional rewriting on the output events if applicable.
          }
          ProvidesEvent(outputFieldNames = outputType.getDeclaredFields.map(_.getName).toSeq, outputType = outputType, outputEventClasses = outputEventClasses)
        }
        //ProvidesNothing
        else ProvidesNothing

      implicit def transformFailureStrategy(recipeStrategy: com.ing.baker.recipe.common.InteractionFailureStrategy): InteractionFailureStrategy = {
        recipeStrategy match {
          case com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff(initialTimeout: Duration, backoffFactor: Double, maximumRetries: Int) => InteractionFailureStrategy.RetryWithIncrementalBackoff(initialTimeout, backoffFactor, maximumRetries)
          case com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction => InteractionFailureStrategy.BlockInteraction
          case _ => InteractionFailureStrategy.BlockInteraction
        }
      }

      def transformEventOutputTransformers[A: ClassTag, B: ClassTag](recipeEventOutputTransformer: com.ing.baker.recipe.common.EventOutputTransformer[A, B]): EventOutputTransformer[A, B] =
        EventOutputTransformer[A, B](recipeEventOutputTransformer.fn)

      implicit def transformEventOutputTransformersMap(eventOutputTransformersMap: Map[Class[_], com.ing.baker.recipe.common.EventOutputTransformer[_, _]]): Map[Class[_], EventOutputTransformer[_, _]] =
        eventOutputTransformersMap.map(e => (e._1, transformEventOutputTransformers(e._2))).toMap

      implicit def transformActionType(recipeActionType: com.ing.baker.recipe.common.ActionType): ActionType = {
        recipeActionType match {
          case com.ing.baker.recipe.common.ActionType.InteractionAction => InteractionAction
          case com.ing.baker.recipe.common.ActionType.SieveAction => SieveAction
        }
      }

      InteractionTransition[Any](
        method = method,
        providesType = providesType,

        inputFields = inputFields,
        interactionClass = interactionClass,
        interactionProvider = implementationProvider,
        interactionName = interactionDescriptor.name,
//        interactionOutputName = interactionOutputName,

        predefinedParameters = interactionDescriptor.predefinedIngredients,
        maximumInteractionCount = interactionDescriptor.maximumInteractionCount,
        failureStrategy = interactionDescriptor.failureStrategy.getOrElse[com.ing.baker.recipe.common.InteractionFailureStrategy](defaultFailureStrategy),
        eventOutputTransformers = interactionDescriptor.eventOutputTransformers,
        actionType = interactionDescriptor.actionType,
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
