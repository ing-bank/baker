package com.ing.baker.recipe

import java.lang.reflect.{Method, Type}

import com.ing.baker.recipe.javadsl.ReflectionHelpers._
import com.ing.baker.types.{BType, Converters}

package object javadsl {

  def createIngredient(ingredientName: String, ingredientType: BType): common.Ingredient =
    new common.Ingredient(
      name = ingredientName,
      ingredientType = ingredientType
  )

  def parseType(jType: Type, errorMessage: String) = {
    try {
      Converters.readJavaType(jType)
    } catch {
      case e: Exception => throw new IllegalArgumentException(errorMessage, e)
    }
  }

  def eventClassToCommonEvent(eventClass: Class[_], firingLimit: Option[Integer]): common.Event =
    new common.Event {
      override val name: String = eventClass.getSimpleName
      override val providedIngredients: Seq[common.Ingredient] =
        eventClass.getDeclaredFields
          .filter(field => !field.isSynthetic)
          .map(f => createIngredient(f.getName, parseType(f.getGenericType, s"Illegal type for ingredient '${f.getName}' on event '${eventClass.getSimpleName}'")))
      override val maxFiringLimit: Option[Integer] = firingLimit
    }

  def interactionClassToCommonInteraction(interactionClass: Class[_ <: Interaction]): common.Interaction =
    new common.Interaction {
      override val name: String = interactionClass.getSimpleName

      private val interactionMethodName: String = "apply"
      private val method: Method = interactionClass.getDeclaredMethods
        .find(_.getName == interactionMethodName)
        .getOrElse(throw new IllegalStateException(
          s"No method named '$interactionMethodName' defined on '${interactionClass.getName}'"))

      override val inputIngredients: Seq[common.Ingredient] =
        method.getParameterNames.map(s => createIngredient(s, parseType(method.parameterTypeForName(s).get, s"Illegal type for ingredient '$s' on interaction '${interactionClass.getName}'")))

      override val output: common.InteractionOutput = {
        if(method.isAnnotationPresent(classOf[annotations.ProvidesIngredient]) && method.isAnnotationPresent(classOf[annotations.FiresEvent]))
          throw new common.RecipeValidationException(s"Interaction $name has both ProvidesIngredient and FiresEvent annotation, only one if possible")
        //ProvidesIngredient
        else if (method.isAnnotationPresent(classOf[annotations.ProvidesIngredient])) {
          val interactionOutputName: String = method.getAnnotation(classOf[annotations.ProvidesIngredient]).value()
          common.ProvidesIngredient(createIngredient(interactionOutputName, parseType(method.getGenericReturnType, s"Illegal return type for interaction '${interactionClass.getSimpleName}'")))
        }
        //ProvidesEvent
        else if (method.isAnnotationPresent(classOf[annotations.FiresEvent])) {
          val outputEventClasses: Seq[Class[_]] = method.getAnnotation(classOf[annotations.FiresEvent]).oneOf()
          val events: Seq[common.Event] = outputEventClasses.map(eventClassToCommonEvent(_, None))
          common.FiresOneOfEvents(events: _*)
        }
        //ProvidesNothing
        else common.ProvidesNothing
      }
    }
}
