package com.ing.baker.recipe

import java.lang.reflect.Method

import com.ing.baker.recipe.common.{FiresOneOfEvents, ProvidesIngredient, ProvidesNothing}
import com.ing.baker.recipe.javadsl.ReflectionHelpers._


package object javadsl {
  def eventClassToCommonEvent(eventClass: Class[_ <:Event]): common.Event =
    new common.Event {
    override val name: String = eventClass.getSimpleName
    override val providedIngredients: Seq[common.Ingredient] = eventClass.getDeclaredFields.map(f => Ingredient(f.getName, f.getType))
  }

  def interactionClassToCommonInteraction(interactionClass: Class[_ <: Interaction]) : common.Interaction =
    new common.Interaction {
      override val name: String = interactionClass.getSimpleName

      private val interactionMethodName: String = "apply"
      private val method: Method = interactionClass.getDeclaredMethods
        .find(_.getName == interactionMethodName)
        .getOrElse(throw new IllegalStateException(
          s"No method named '$interactionMethodName' defined on '${interactionClass.getName}'"))

      override val inputIngredients: Seq[common.Ingredient] = method.getParameterNames.map(s => Ingredient(s, method.parameterTypeForName(s).get))

      override val output: common.InteractionOutput = {
        //ProvidesIngredient
        if(method.isAnnotationPresent(classOf[annotations.ProvidesIngredient]))
        {
          val interactionOutputName: String = method.getAnnotation(classOf[annotations.ProvidesIngredient]).value()
          ProvidesIngredient(Ingredient(interactionOutputName, method.getReturnType))
        }
        //ProvidesEvent
        else if(method.isAnnotationPresent(classOf[annotations.FiresEvent])) {
          val outputEventClasses: Seq[Class[_ <: Event]] = method.getAnnotation(classOf[annotations.FiresEvent]).oneOf().toSeq
          val events: Seq[common.Event] = outputEventClasses.map(eventClassToCommonEvent)
          FiresOneOfEvents(events)
        }
        //ProvidesNothing
        else ProvidesNothing
      }
    }
}
