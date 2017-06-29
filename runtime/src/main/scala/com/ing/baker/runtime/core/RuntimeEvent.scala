package com.ing.baker.runtime.core

import com.ing.baker.il.{IngredientType, EventType}
import com.ing.baker.runtime.core.RuntimeEvent.log
import com.ing.baker.runtime.event_extractors.{CompositeEventExtractor, EventExtractor}
import org.slf4j.LoggerFactory


case class RuntimeEvent(name: String,
                        providedIngredients: Map[String, Any]) {

  def toCompiledEvent: EventType = {
    EventType(name, providedIngredients.map(pi => IngredientType(pi._1, pi._2.getClass)).toSeq)
  }

  def validate(eventType: EventType): RuntimeEvent = {
    val correctIngredients = providedIngredients.filter {
      case (name, value) => eventType.providedIngredients.find(_.name equals name) match {
        case Some(compiledIngredient) => compiledIngredient.clazz.isAssignableFrom(value.getClass)
        case None => false
      }
    }
    val missingIngredients: Seq[IngredientType] = eventType.providedIngredients.filter(p => !correctIngredients.contains(p.name))
    if(missingIngredients.nonEmpty) {
      log.error(
        s"""
           |Event: $name fired by an interaction but does not provide all required ingredients
           |Missing ingredients: ${missingIngredients.mkString(",")}
           |Event it should match : $eventType
           |Ingredients found : ${correctIngredients.mkString(",")}
         """.stripMargin)
    }
    RuntimeEvent(eventType.name, correctIngredients ++ missingIngredients.map(i => i.name -> null))
  }
}

object RuntimeEvent {

  private val log = LoggerFactory.getLogger("com.ing.baker.compiledRecipe.petrinet.EventSource")

  private val eventExtractor: EventExtractor = new CompositeEventExtractor()
}
