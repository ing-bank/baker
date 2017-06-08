package com.ing.baker.compiledRecipe.petrinet

import com.ing.baker.compiledRecipe.{CompiledEvent, CompiledIngredient}
import com.ing.baker.compiledRecipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.core.ProcessState
import org.slf4j.LoggerFactory

object EventSource {

  private val log = LoggerFactory.getLogger("com.ing.baker.compiledRecipe.petrinet.EventSource")

  /**
    * Extracts ingredients from the given event object.
    * It filters out all possible events that do not match with any expected ingredient for the event
    * It checks if all ingredients are provided that the event should provide, if not create the ingredients with value null
    * @param firedEvent the event to extract ingredients from
    * @param ingredientExtractor the ingredient extractor to help getting the fields from the firedEvent
    * @return
    */
  def extractIngredientsFromEventIfValid(firedEvent: Any, eventToComplyTo: CompiledEvent, ingredientExtractor: IngredientExtractor) : Map[String, Any] = {
      //Find the possible ingredients
      val possibleIngredients: Map[String, Any] = ingredientExtractor.extractIngredientData(firedEvent)
      val isInFoundEvent: String => Boolean = s => eventToComplyTo.providedIngredients.exists(i => i.name equals s)
      val ingredients = possibleIngredients.filter(i => isInFoundEvent(i._1))
      val missingIngredients: Seq[CompiledIngredient] = eventToComplyTo.providedIngredients.filter(p => !ingredients.contains(p.name))
      if(missingIngredients.nonEmpty){
        log.warn(
          s"""
             |Event: $firedEvent fired by an interaction but does not provide all required ingredients
             |Missing ingredients: ${missingIngredients.mkString(",")}
             |Event it should match : $eventToComplyTo
             |Ingredients found : ${ingredients.mkString(",")}
         """.stripMargin)
        ingredients ++ missingIngredients.map(i => i.name -> null)
      }
      else ingredients
  }

  def updateIngredientState[I](interactionTransition: InteractionTransition[I], ingredientExtractor: IngredientExtractor): (ProcessState) => (Any) => ProcessState =
    state =>
      event => {
        interactionTransition.providesType match {
          case _ if event == null => state
          case ProvidesIngredient(ingredient) =>
            state.copy(ingredients = state.ingredients + (ingredient.name -> event))
          case FiresOneOfEvents(events) =>
            val optionalFoundEvent: Option[CompiledEvent] = events.find(e => e.name equals event.getClass.getSimpleName)
            if (optionalFoundEvent.isDefined) state.copy(ingredients = state.ingredients ++ extractIngredientsFromEventIfValid(event, optionalFoundEvent.get, ingredientExtractor))
            else {
              log.error(s"Event: $event fired by an interaction that does not fire any events")
              state
            }
          case ProvidesNothing => state
          case _ => state
        }
      }

  def updateEventState(eventTransition: EventTransition, ingredientExtractor: IngredientExtractor): (ProcessState) => (Any) => ProcessState =
    state =>
      event => {
        //Only extract ingredients if they are fired by a sensory events
        //If it is a interaction provided event then the ingredients are provided by the Interaction.
        //This is done because at that point a check can be done if the provided Ingredients are valid for the Interaction
        if(eventTransition.isSensoryEvent) {
          val eventIngredients = extractIngredientsFromEventIfValid(event, eventTransition.event, ingredientExtractor)
          state.copy(ingredients = state.ingredients ++ eventIngredients)
        }
        else state
      }
}
