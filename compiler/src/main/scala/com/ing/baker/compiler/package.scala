package com.ing.baker

import com.ing.baker.il._
import com.ing.baker.il.failurestrategy.InteractionFailureStrategy
import com.ing.baker.il.petrinet._
import com.ing.baker.types._
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy.{FireEventAfterFailure, RetryWithIncrementalBackoff}
import com.ing.baker.recipe.common.{InteractionDescriptor, ProvidesNothing}

import scala.concurrent.duration.Duration

package object compiler {

  def ingredientToCompiledIngredient(ingredient: common.Ingredient): RecordField = RecordField(ingredient.name, ingredient.ingredientType)

  def eventToCompiledEvent(event: common.Event): EventType = EventType(event.name, event.providedIngredients.map(ingredientToCompiledIngredient))

  implicit class InteractionOps(interaction: InteractionDescriptor) {

    def toInteractionTransition(defaultFailureStrategy: common.InteractionFailureStrategy, allIngredientNames: Set[String]): InteractionTransition[_] =
      interactionTransitionOf(interaction, defaultFailureStrategy, ActionType.InteractionAction, allIngredientNames)

    def toSieveTransition(defaultFailureStrategy: common.InteractionFailureStrategy, allIngredientNames: Set[String]): InteractionTransition[_] =
      interactionTransitionOf(interaction, defaultFailureStrategy, ActionType.SieveAction, allIngredientNames)

    def interactionTransitionOf(
                                 interactionDescriptor: InteractionDescriptor,
                                 defaultFailureStrategy: common.InteractionFailureStrategy,
                                 actionType: ActionType,
                                 allIngredientNames: Set[String]): InteractionTransition[Any] = {

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

      def transformFailureStrategy(recipeStrategy: common.InteractionFailureStrategy): InteractionFailureStrategy = {
        recipeStrategy match {
          case common.InteractionFailureStrategy.RetryWithIncrementalBackoff(initialTimeout: Duration, backoffFactor: Double, maximumRetries: Int, maxTimeBetweenRetries: Option[Duration], retryExhaustedEvent: Option[common.Event]) =>
            il.failurestrategy.RetryWithIncrementalBackoff(initialTimeout, backoffFactor, maximumRetries, maxTimeBetweenRetries, if(retryExhaustedEvent.isDefined) Some(EventType(retryExhaustedEvent.get.name, Seq.empty)) else None)
          case common.InteractionFailureStrategy.BlockInteraction() => il.failurestrategy.BlockInteraction
          case common.InteractionFailureStrategy.FireEventAfterFailure(event) => il.failurestrategy.FireEventAfterFailure(EventType(event.name, Seq.empty))
          case _ => il.failurestrategy.BlockInteraction
        }
      }

      def transformEventOutputTransformer(recipeEventOutputTransformer: common.EventOutputTransformer): EventOutputTransformer =
        EventOutputTransformer(recipeEventOutputTransformer.newEventName, recipeEventOutputTransformer.ingredientRenames)

      def transformEventToCompiledEvent(event: common.Event): EventType = {
        EventType(
          event.name,
          event.providedIngredients.map(ingredientToCompiledIngredient))
      }

      //Replace ProcessId to ProcessIdName tag as know in compiledRecipe-
      //Replace ingredient tags with overridden tags
      val inputFields: Seq[(String, Type)] = interactionDescriptor.interaction.inputIngredients
        .map { ingredient =>
          if(ingredient.name == common.ProcessIdName) il.processIdName -> ingredient.ingredientType
          else interactionDescriptor.overriddenIngredientNames.getOrElse(ingredient.name, ingredient.name) -> ingredient.ingredientType
        }

      val exhaustedRetryEvent = interactionDescriptor.failureStrategy.flatMap {
        case RetryWithIncrementalBackoff(_, _, _, _, optionalExhaustedRetryEvent) => optionalExhaustedRetryEvent
        case FireEventAfterFailure(event) => Some(event)
        case _ => None
      }.map(transformEventToCompiledEvent)

      val (originalEvents, eventsToFire, providedIngredientEvent): (Seq[EventType], Seq[EventType], Option[EventType]) =
        interactionDescriptor.interaction.output match {
          case common.ProvidesIngredient(outputIngredient) =>
            val ingredientName: String =
              if(interactionDescriptor.overriddenOutputIngredientName.nonEmpty) interactionDescriptor.overriddenOutputIngredientName.get
              else outputIngredient.name
            val event = EventType(interactionDescriptor.name + "Successful", Seq(RecordField(ingredientName, outputIngredient.ingredientType)))
            val events = Seq(event)
            (events, events, Some(event))
          case common.FiresOneOfEvents(events @ _*) =>
            val originalCompiledEvents = events.map(transformEventToCompiledEvent)
            val compiledEvents = events.map(transformEventType).map(transformEventToCompiledEvent)
            (originalCompiledEvents, compiledEvents, None)
          case ProvidesNothing => (Seq.empty, Seq.empty, None)
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


      InteractionTransition[Any](
        eventsToFire = eventsToFire ++ exhaustedRetryEvent,
        originalEvents = originalEvents ++ exhaustedRetryEvent,
        providedIngredientEvent = providedIngredientEvent,
        requiredIngredients = inputFields.map { case (name, ingredientType) => RecordField(name, ingredientType) },
        interactionName = interactionDescriptor.name,
        originalInteractionName = interactionDescriptor.interaction.name,
        predefinedParameters = predefinedIngredientsWithOptionalsEmpty,
        maximumInteractionCount = interactionDescriptor.maximumInteractionCount,
        failureStrategy = transformFailureStrategy(interactionDescriptor.failureStrategy.getOrElse[common.InteractionFailureStrategy](defaultFailureStrategy)),
        eventOutputTransformers =  interactionDescriptor.eventOutputTransformers.map { case (event, transformer) => eventToCompiledEvent(event) -> transformEventOutputTransformer(transformer) },
        actionType = actionType)
    }
  }

  implicit class TransitionOps(transitions: Seq[Transition[_, _]]) {

    def findTransitionsByClass: Class[_] ⇒ Option[Transition[_, _]] =
      clazz => transitions.findByLabel(clazz.getSimpleName)

    def findTransitionByName: String ⇒ Option[Transition[_, _]] =
      interactionName ⇒ transitions.findByLabel(interactionName)
  }

  implicit class EventTransitionOps(eventTransitions: Seq[EventTransition]) {
    def findEventTransitionsByEvent: EventType ⇒ Option[EventTransition] =
      event => eventTransitions.find(_.event == event)
    def findEventTransitionsByEventName: String ⇒ Option[EventTransition] =
      eventName => eventTransitions.find(_.event.name == eventName)
  }

}
