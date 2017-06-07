package com.ing.baker

import com.ing.baker.compiledRecipe.ActionType.{InteractionAction, SieveAction}
import com.ing.baker.compiledRecipe.petrinet.{EventTransition, FiresOneOfEvents, InteractionTransition, ProvidesIngredient, ProvidesNothing, ProvidesType, Transition}
import com.ing.baker.compiledRecipe.{ActionType, InteractionFailureStrategy, RuntimeEvent, RuntimeEventOutputTransformer, RuntimeIngredient}
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.{Event, Ingredient, InteractionDescriptor}
import io.kagera.api._

import scala.concurrent.duration.Duration

package object compiler {

  def ingredientsToRuntimeIngredient(ingredient: common.Ingredient): RuntimeIngredient = RuntimeIngredient(ingredient.name, ingredient.clazz)

  def eventToRuntimeEvent(event: common.Event): RuntimeEvent = RuntimeEvent(event.name, event.providedIngredients.map(ingredientsToRuntimeIngredient))

  def runtimeIngredientToIngredient(ingredient: RuntimeIngredient): common.Ingredient = new Ingredient {
    override val name: String = ingredient.name
    override val clazz: Class[_] = ingredient.clazz
  }

  def runtimeEventToEvent(runtimeEvent: RuntimeEvent): common.Event = new Event {
    override val name: String = runtimeEvent.name
    override val providedIngredients: Seq[Ingredient] = runtimeEvent.providedIngredients.map(runtimeIngredientToIngredient)
  }

  implicit class InteractionOps(interaction: InteractionDescriptor) {

    def toInteractionTransition(defaultFailureStrategy: com.ing.baker.recipe.common.InteractionFailureStrategy): (InteractionTransition[_], Seq[String]) = {

      val validationErrors = scala.collection.mutable.MutableList.empty[String]

      val interactionTransition = interactionTransitionOf(interaction, defaultFailureStrategy)

      (interactionTransition, validationErrors)
    }

    def interactionTransitionOf(
                                 interactionDescriptor: InteractionDescriptor,
                                 defaultFailureStrategy: com.ing.baker.recipe.common.InteractionFailureStrategy): InteractionTransition[Any] = {

      val inputFields: Seq[(String, Class[_])] = interactionDescriptor.interaction.inputIngredients
        //Replace ProcessId to ProcessIdName tag as know in compiledRecipe
        //Replace ingredient tags with overridden tags
        .map(ingredient =>
          if(ingredient.name == common.ProcessIdName) compiledRecipe.processIdName -> ingredient.clazz
          else interactionDescriptor.overriddenIngredientNames.getOrElse(ingredient.name, ingredient.name) -> ingredient.clazz)

      def transformEventType(event: common.Event): common.Event =
        interactionDescriptor.eventOutputTransformers
            .find(e => e.originalEvent.equals(event))
        match {
          case Some(eventOutputTransformer) => eventOutputTransformer.newEvent
          case _ => event
        }

      val providesType: ProvidesType =
        interactionDescriptor.interaction.output match{
          case common.ProvidesIngredient(outputIngredient) => {
            val ingredientName: String =
              if(interactionDescriptor.overriddenOutputIngredientName.nonEmpty) interactionDescriptor.overriddenOutputIngredientName.get
              else outputIngredient.name
            ProvidesIngredient(RuntimeIngredient(ingredientName, outputIngredient.clazz))
          }
          case common.FiresOneOfEvents(events) => {
            val runtimeEvents = events.map(transformEventType)
              .map(e => RuntimeEvent(e.name, e.providedIngredients
                .map(i => RuntimeIngredient(i.name, i.clazz))))
            FiresOneOfEvents(runtimeEvents)
          }
          case common.ProvidesNothing => ProvidesNothing
        }

      implicit def transformFailureStrategy(recipeStrategy: com.ing.baker.recipe.common.InteractionFailureStrategy): InteractionFailureStrategy = {
        recipeStrategy match {
          case com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff(initialTimeout: Duration, backoffFactor: Double, maximumRetries: Int) => InteractionFailureStrategy.RetryWithIncrementalBackoff(initialTimeout, backoffFactor, maximumRetries)
          case com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction => InteractionFailureStrategy.BlockInteraction
          case _ => InteractionFailureStrategy.BlockInteraction
        }
      }

      def transformEventOutputTransformer(recipeEventOutputTransformer: common.OutputTransformer): RuntimeEventOutputTransformer = {
        RuntimeEventOutputTransformer(eventToRuntimeEvent(
          recipeEventOutputTransformer.originalEvent),
          eventToRuntimeEvent(recipeEventOutputTransformer.newEvent),
          (runtimeEventToEvent _).andThen(recipeEventOutputTransformer.fn).andThen(eventToRuntimeEvent)
        )
      }

      def transformActionType(interactionDescriptor: common.InteractionDescriptor): ActionType = {
        interactionDescriptor.actionType match {
          case common.InteractionAction => InteractionAction
          case common.SieveAction => SieveAction
        }
      }

      InteractionTransition[Any](
        providesType = providesType,
        inputFields = inputFields,
        interactionName = interactionDescriptor.name,
        predefinedParameters = interactionDescriptor.predefinedIngredients,
        maximumInteractionCount = interactionDescriptor.maximumInteractionCount,
        failureStrategy = interactionDescriptor.failureStrategy.getOrElse[com.ing.baker.recipe.common.InteractionFailureStrategy](defaultFailureStrategy),
        eventOutputTransformers =  interactionDescriptor.eventOutputTransformers.map(et => eventToRuntimeEvent(et.originalEvent) -> transformEventOutputTransformer(et)).toMap,
        actionType = transformActionType(interactionDescriptor))
    }
  }

  implicit class TransitionOps(transitions: Seq[Transition[_, _, _]]) {

    def findTransitionsByClass: Class[_] ⇒ Option[Transition[_, _, _]] =
      clazz => transitions.findByLabel(clazz.getSimpleName)

    def findTransitionByName: String ⇒ Option[Transition[_, _, _]] =
      interactionName ⇒ transitions.findByLabel(interactionName)
  }

  implicit class EventTransitionOps(eventTransitions: Seq[EventTransition]) {
    def findEventTransitionsByEvent: RuntimeEvent ⇒ Option[EventTransition] =
      event => eventTransitions.find(_.event == event)
  }
}
