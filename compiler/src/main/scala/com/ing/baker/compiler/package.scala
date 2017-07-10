package com.ing.baker

import com.ing.baker.il.petrinet.{EventTransition, FiresOneOfEvents, InteractionTransition, ProvidesIngredient, ProvidesNothing, ProvidesType, Transition}
import com.ing.baker.il.{ActionType, EventOutputTransformer, EventType, IngredientType, InteractionFailureStrategy}
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionDescriptor
import io.kagera.api._

import scala.concurrent.duration.Duration

package object compiler {

  def ingredientsToRuntimeIngredient(ingredient: common.Ingredient): IngredientType = IngredientType(ingredient.name, ingredient.clazz)

  def eventToCompiledEvent(event: common.Event): EventType = EventType(event.name, event.providedIngredients.map(ingredientsToRuntimeIngredient))

  implicit class InteractionOps(interaction: InteractionDescriptor) {

    def toInteractionTransition(defaultFailureStrategy: com.ing.baker.recipe.common.InteractionFailureStrategy): (InteractionTransition[_], Seq[String]) = {

      val validationErrors = scala.collection.mutable.MutableList.empty[String]

      val interactionTransition = interactionTransitionOf(interaction, defaultFailureStrategy, ActionType.InteractionAction)

      (interactionTransition, validationErrors)
    }

    def toSieveTransition(defaultFailureStrategy: com.ing.baker.recipe.common.InteractionFailureStrategy): (InteractionTransition[_], Seq[String]) = {

      val validationErrors = scala.collection.mutable.MutableList.empty[String]

      val interactionTransition = interactionTransitionOf(interaction, defaultFailureStrategy, ActionType.SieveAction)

      (interactionTransition, validationErrors)
    }

    def interactionTransitionOf(
                                 interactionDescriptor: InteractionDescriptor,
                                 defaultFailureStrategy: com.ing.baker.recipe.common.InteractionFailureStrategy,
                                 actionType: ActionType): InteractionTransition[Any] = {

      //This transforms the event using the eventOutputTransformer to the new event
      //If there is no eventOutputTransformer for the event the original event is returned
      def transformEventType(event: common.Event): common.Event =
        interactionDescriptor.eventOutputTransformers.get(event)
        match {
          case Some(eventOutputTransformer) =>
            new common.Event {
              override val name: String = eventOutputTransformer.newEventName
              override val providedIngredients: Seq[common.Ingredient] = event.providedIngredients.map(i =>
                new common.Ingredient {
                  override val name: String = eventOutputTransformer.ingredientRenames.getOrElse(i.name, i.name)
                  override val clazz: Class[_] = i.clazz
                })
            }
          case _ => event
        }

      def transformFailureStrategy(recipeStrategy: com.ing.baker.recipe.common.InteractionFailureStrategy): InteractionFailureStrategy = {
        recipeStrategy match {
          case com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff(initialTimeout: Duration, backoffFactor: Double, maximumRetries: Int) => InteractionFailureStrategy.RetryWithIncrementalBackoff(initialTimeout, backoffFactor, maximumRetries)
          case com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction => InteractionFailureStrategy.BlockInteraction
          case _ => InteractionFailureStrategy.BlockInteraction
        }
      }

      def transformEventOutputTransformer(recipeEventOutputTransformer: common.EventOutputTransformer): EventOutputTransformer = {
        EventOutputTransformer(recipeEventOutputTransformer.newEventName, recipeEventOutputTransformer.ingredientRenames
        )
      }

      def transformEventToCompiledEvent(event: common.Event): EventType = {
        EventType(
          event.name,
          event.providedIngredients
            .map(i => IngredientType(i.name, i.clazz)))
      }

      val inputFields: Seq[(String, Class[_])] = interactionDescriptor.interaction.inputIngredients
        //Replace ProcessId to ProcessIdName tag as know in compiledRecipe
        //Replace ingredient tags with overridden tags
        .map(ingredient =>
        if(ingredient.name == common.ProcessIdName) il.processIdName -> ingredient.clazz
        else interactionDescriptor.overriddenIngredientNames.getOrElse(ingredient.name, ingredient.name) -> ingredient.clazz)


      val providesType: ProvidesType =
        interactionDescriptor.interaction.output match {
          case common.ProvidesIngredient(outputIngredient) =>
            val ingredientName: String =
              if(interactionDescriptor.overriddenOutputIngredientName.nonEmpty) interactionDescriptor.overriddenOutputIngredientName.get
              else outputIngredient.name
            ProvidesIngredient(IngredientType(ingredientName, outputIngredient.clazz))
          case common.FiresOneOfEvents(events) =>
            val originalCompiledEvents = events.map(transformEventToCompiledEvent)
            val compiledEvents = events.map(transformEventType).map(transformEventToCompiledEvent)
            FiresOneOfEvents(compiledEvents, originalCompiledEvents)
          case common.ProvidesNothing() => ProvidesNothing
        }

      InteractionTransition[Any](
        providesType = providesType,
        inputFields = inputFields,
        interactionName = interactionDescriptor.name,
        originalInteractionName = interactionDescriptor.interaction.name,
        predefinedParameters = interactionDescriptor.predefinedIngredients,
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
  }
}
