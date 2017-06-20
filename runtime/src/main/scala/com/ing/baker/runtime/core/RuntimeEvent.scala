package com.ing.baker.runtime.core

import com.ing.baker.il.{CompiledEvent, CompiledIngredient}
import com.ing.baker.runtime.ingredient_extractors.{CompositeIngredientExtractor, IngredientExtractor}
import org.slf4j.LoggerFactory


case class RuntimeEvent(name: String,
                        providedIngredients: Map[String, Any]) {
  def toCompiledEvent: CompiledEvent = {
    CompiledEvent(name, providedIngredients.map(pi => CompiledIngredient(pi._1, pi._2.getClass)).toSeq)
  }
}

object RuntimeEvent {

  private val log = LoggerFactory.getLogger("com.ing.baker.compiledRecipe.petrinet.EventSource")

  private val ingredientExtractor: IngredientExtractor = new CompositeIngredientExtractor()

  /**
    * Creates a event and extracts ingredients from the given object.
    * It filters out all possible ingredients that do not match with any expected ingredient for the event
    * It also filters out all ingredients of the wrong type.
    * It checks if all ingredients are provided that the event should provide, if not create the ingredients with value null
    * @param firedEvent the event to extract ingredients from
    * @return
    */
  def forEvent(firedEvent: Any, eventToComplyTo: CompiledEvent): RuntimeEvent = {
    val foundIngredients: Map[String, Any] = ingredientExtractor.extractIngredientData(firedEvent)
    //Filter out all ingredients where the name does not comply to any ingredient name
    //Filter out all ingredients where the type does not comply to the found ingredient
    val correctIngredients = foundIngredients.filter {
      case (name, value) => eventToComplyTo.providedIngredients.find(_.name equals name) match {
        case Some(compiledIngredient) => compiledIngredient.clazz.isAssignableFrom(value.getClass)
        case None => false
      }
    }
    val missingIngredients: Seq[CompiledIngredient] = eventToComplyTo.providedIngredients.filter(p => !correctIngredients.contains(p.name))
    if(missingIngredients.nonEmpty) {
      log.error(
        s"""
           |Event: $firedEvent fired by an interaction but does not provide all required ingredients
           |Missing ingredients: ${missingIngredients.mkString(",")}
           |Event it should match : $eventToComplyTo
           |Ingredients found : ${correctIngredients.mkString(",")}
         """.stripMargin)
    }
    RuntimeEvent(eventToComplyTo.name, correctIngredients ++ missingIngredients.map(i => i.name -> null))
  }

  def forIngredient(firedInteractionName: String, providedIngredient: Any, ingredientToComplyTo: CompiledIngredient): RuntimeEvent = {
    if(ingredientToComplyTo.clazz.isAssignableFrom(providedIngredient.getClass))
      RuntimeEvent(s"$firedInteractionName:${ingredientToComplyTo.name}", Map(ingredientToComplyTo.name -> providedIngredient))
    //TODO Decide what to do when the ingredient is not of the correct typing, for now a Ingredient is create with a null value
    else {
      log.error(
        s"""
           |Ingredient: ${ingredientToComplyTo.name} provided by an interaction but does not comply to the expected type
           |Expected  : $ingredientToComplyTo
           |Provided  : $providedIngredient
         """.stripMargin)
      RuntimeEvent(s"$firedInteractionName:${ingredientToComplyTo.name}", Map(ingredientToComplyTo.name -> null))
    }
  }

  def forNothing(interactionName: String) : RuntimeEvent = {
    RuntimeEvent(s"$interactionName:ProvidedNothing", Map.empty)
  }
}
