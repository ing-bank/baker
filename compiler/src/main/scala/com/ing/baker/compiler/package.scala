package com.ing.baker

import com.ing.baker.il._
import com.ing.baker.il.failurestrategy.InteractionFailureStrategy
import com.ing.baker.il.petrinet._
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionDescriptor
import com.ing.baker.types._

package object compiler {

  def ingredientToCompiledIngredient(ingredient: common.Ingredient): IngredientDescriptor = IngredientDescriptor(ingredient.name, ingredient.ingredientType)

  def eventToCompiledEvent(event: common.Event): EventDescriptor = EventDescriptor(event.name, event.providedIngredients.map(ingredientToCompiledIngredient))

  implicit class InteractionOps(interaction: InteractionDescriptor) {

    def toInteractionTransition(defaultFailureStrategy: common.InteractionFailureStrategy, allIngredientNames: Set[String]): InteractionTransition =
      interactionTransitionOf(interaction, defaultFailureStrategy, allIngredientNames)

    def interactionTransitionOf(interactionDescriptor: InteractionDescriptor,
                                defaultFailureStrategy: common.InteractionFailureStrategy,
                                allIngredientNames: Set[String]): InteractionTransition = {

      //This transforms the event using the eventOutputTransformer to the new event
      //If there is no eventOutputTransformer for the event the original event is returned
      def transformEventType(event: common.Event): common.Event =
      interactionDescriptor.eventOutputTransformers.get(event)
      match {
        case Some(eventOutputTransformer) =>
          new common.Event {
            override val name: String = eventOutputTransformer.newEventName
            override val providedIngredients: Seq[common.Ingredient] = event.providedIngredients.map(i =>
              new common.Ingredient(eventOutputTransformer.ingredientRenames.getOrElse(i.name, i.name), i.ingredientType))
          }
        case _ => event
      }

      def transformEventOutputTransformer(recipeEventOutputTransformer: common.EventOutputTransformer): EventOutputTransformer =
        EventOutputTransformer(recipeEventOutputTransformer.newEventName, recipeEventOutputTransformer.ingredientRenames)

      def transformEventToCompiledEvent(event: common.Event): EventDescriptor = {
        EventDescriptor(
          event.name,
          event.providedIngredients.map(ingredientToCompiledIngredient))
      }

      //Replace ProcessId to ProcessIdName tag as know in compiledRecipe-
      //Replace ingredient tags with overridden tags
      val inputFields: Seq[(String, Type)] = interactionDescriptor.inputIngredients
        .map { ingredient =>
          if (ingredient.name == common.processIdName) il.processIdName -> ingredient.ingredientType
          else interactionDescriptor.overriddenIngredientNames.getOrElse(ingredient.name, ingredient.name) -> ingredient.ingredientType
        }

      val (originalEvents, eventsToFire): (Seq[EventDescriptor], Seq[EventDescriptor]) = {
        val originalCompiledEvents = interactionDescriptor.output.map(transformEventToCompiledEvent)
        val compiledEvents = interactionDescriptor.output.map(transformEventType).map(transformEventToCompiledEvent)
        (originalCompiledEvents, compiledEvents)
      }

      //For each ingredient that is not provided
      //And is of the type Optional or Option
      //Add it to the predefinedIngredients List as empty
      //Add the predefinedIngredients later to overwrite any created empty field with the given predefined value.
      val predefinedIngredientsWithOptionalsEmpty: Map[String, Value] =
      inputFields.flatMap {
        case (name, types.OptionType(_)) if !allIngredientNames.contains(name) => Seq(name -> NullValue)
        case _ => Seq.empty
      }.toMap ++ interactionDescriptor.predefinedIngredients

      val (failureStrategy: InteractionFailureStrategy, exhaustedRetryEvent: Option[EventDescriptor]) = {
        interactionDescriptor.failureStrategy.getOrElse[common.InteractionFailureStrategy](defaultFailureStrategy) match {
          case common.InteractionFailureStrategy.RetryWithIncrementalBackoff(initialTimeout, backoffFactor, maximumRetries, maxTimeBetweenRetries, fireRetryExhaustedEvent) =>
            val exhaustedRetryEvent: Option[EventDescriptor] = fireRetryExhaustedEvent match {
              case Some(None)            => Some(EventDescriptor(interactionDescriptor.name + exhaustedEventAppend, Seq.empty))
              case Some(Some(eventName)) => Some(EventDescriptor(eventName, Seq.empty))
              case None                  => None
            }
            (il.failurestrategy.RetryWithIncrementalBackoff(initialTimeout, backoffFactor, maximumRetries, maxTimeBetweenRetries, exhaustedRetryEvent), exhaustedRetryEvent)
          case common.InteractionFailureStrategy.BlockInteraction() => (
            il.failurestrategy.BlockInteraction, None)
          case common.InteractionFailureStrategy.FireEventAfterFailure(eventNameOption) =>
            val eventName = eventNameOption.getOrElse(interactionDescriptor.name + exhaustedEventAppend)
            val exhaustedRetryEvent: EventDescriptor = EventDescriptor(eventName, Seq.empty)
            (il.failurestrategy.FireEventAfterFailure(exhaustedRetryEvent), Some(exhaustedRetryEvent))
          case _ => (il.failurestrategy.BlockInteraction, None)
        }
      }

      InteractionTransition(
        eventsToFire = eventsToFire ++ exhaustedRetryEvent,
        originalEvents = originalEvents ++ exhaustedRetryEvent,
        requiredIngredients = inputFields.map { case (name, ingredientType) => IngredientDescriptor(name, ingredientType) },
        interactionName = interactionDescriptor.name,
        originalInteractionName = interactionDescriptor.originalName,
        predefinedParameters = predefinedIngredientsWithOptionalsEmpty,
        maximumInteractionCount = interactionDescriptor.maximumInteractionCount,
        failureStrategy = failureStrategy,
        eventOutputTransformers = interactionDescriptor.eventOutputTransformers.map {
          case (event, transformer) => event.name -> transformEventOutputTransformer(transformer) })
    }
  }
}
