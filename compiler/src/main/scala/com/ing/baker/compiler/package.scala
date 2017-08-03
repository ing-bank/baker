package com.ing.baker

import com.ing.baker.il.failurestrategy.InteractionFailureStrategy
import com.ing.baker.il.petrinet.{EventTransition, FiresOneOfEvents, InteractionTransition, ProvidesIngredient, ProvidesNothing, ProvidesType, Transition}
import com.ing.baker.il.{ActionType, EventOutputTransformer, EventType, IngredientType}
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionDescriptor

import scala.concurrent.duration.Duration

package object compiler {

  def ingredientsToRuntimeIngredient(ingredient: common.Ingredient): IngredientType = IngredientType(ingredient.name, ingredient.clazz)

  def eventToCompiledEvent(event: common.Event): EventType = EventType(event.name, event.providedIngredients.map(ingredientsToRuntimeIngredient))

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
                new common.Ingredient {
                  override val name: String = eventOutputTransformer.ingredientRenames.getOrElse(i.name, i.name)
                  override val clazz: Class[_] = i.clazz
                })
            }
          case _ => event
        }

      def transformFailureStrategy(recipeStrategy: common.InteractionFailureStrategy): InteractionFailureStrategy = {
        recipeStrategy match {
          case common.InteractionFailureStrategy.RetryWithIncrementalBackoff(initialTimeout: Duration, backoffFactor: Double, maximumRetries: Int, maxTimeBetweenRetries: Option[Duration]) =>
            il.failurestrategy.RetryWithIncrementalBackoff(initialTimeout, backoffFactor, maximumRetries, maxTimeBetweenRetries)
          case common.InteractionFailureStrategy.BlockInteraction() => il.failurestrategy.BlockInteraction
          case _ => il.failurestrategy.BlockInteraction
        }
      }

      def transformEventOutputTransformer(recipeEventOutputTransformer: common.EventOutputTransformer): EventOutputTransformer =
        EventOutputTransformer(recipeEventOutputTransformer.newEventName, recipeEventOutputTransformer.ingredientRenames)

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
          case common.ProvidesNothing => ProvidesNothing
        }

      //For each ingredient that is not provided
      //And is of the type Optional or Option
      //Add it to the predefinedIngredients List as empty
      //Add the predefinedIngredients later to overwrite any created empty field with the given predefined value.
      val predefinedIngredientsWithOptionalsEmpty: Map[String, Any] =
        inputFields.flatMap {
          case (name, clazz) if !allIngredientNames.contains(name) && classOf[java.util.Optional[_]].isAssignableFrom(clazz)
              => Seq((name, java.util.Optional.empty()))
          case (name, clazz) if !allIngredientNames.contains(name) && classOf[scala.Option[_]].isAssignableFrom(clazz)
              => Seq((name, scala.Option.empty))
          case _ => Seq.empty
        }.toMap ++ interactionDescriptor.predefinedIngredients

      InteractionTransition[Any](
        providesType = providesType,
        inputFields = inputFields,
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
  }

}
