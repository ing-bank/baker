package com.ing.baker.recipe

import java.lang.reflect.{Method, Type => JType}

import com.ing.baker.recipe.javadsl.ReflectionHelpers._
import com.ing.baker.types.{Converters, Type}

package object javadsl {

  def createIngredient(ingredientName: String, ingredientType: Type): common.Ingredient =
    new common.Ingredient(
      name = ingredientName,
      ingredientType = ingredientType
    )

  def parseType(jType: JType, errorMessage: String) = {
    try {
      Converters.readJavaType(jType)
    } catch {
      case e: Exception => throw new IllegalArgumentException(errorMessage, e)
    }
  }

  def eventClassToCommonEvent(eventClass: Class[_], firingLimit: Option[Int]): common.Event =
    new common.Event {
      override val name: String = eventClass.getSimpleName
      override val providedIngredients: Seq[common.Ingredient] =
        eventClass.getDeclaredFields
          .filter(field => !field.isSynthetic)
          .map(f => createIngredient(f.getName, parseType(f.getGenericType, s"Unsupported type for ingredient '${f.getName}' on event '${eventClass.getSimpleName}'")))
      override val maxFiringLimit: Option[Int] = firingLimit
    }

  def stringToCommonEvent(eventName: String, firingLimit: Option[Int]): common.Event =
    new common.Event {
      override val name: String = eventName
      override val providedIngredients: Seq[common.Ingredient] = Seq.empty
      override val maxFiringLimit: Option[Int] = firingLimit
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
        method.getParameterNames.map(s => createIngredient(s, parseType(method.parameterTypeForName(s).get, s"Unsupported type for ingredient '$s' on interaction '${interactionClass.getName}'")))

      override val output: common.InteractionOutput = {
        if (method.isAnnotationPresent(classOf[annotations.ProvidesIngredient]) && method.isAnnotationPresent(classOf[annotations.FiresEvent]))
          throw new common.RecipeValidationException(s"Interaction $name has both ProvidesIngredient and FiresEvent annotation, only one may be specified")
        //ProvidesIngredient
        else if (method.isAnnotationPresent(classOf[annotations.ProvidesIngredient])) {
          val interactionOutputName: String = method.getAnnotation(classOf[annotations.ProvidesIngredient]).value()
          common.ProvidesIngredient(createIngredient(interactionOutputName, parseType(method.getGenericReturnType, s"Unsupported return type for interaction '${interactionClass.getSimpleName}'")))
        }
        //ProvidesEvent
        else if (method.isAnnotationPresent(classOf[annotations.FiresEvent])) {
          val outputEventClasses: Seq[Class[_]] = method.getAnnotation(classOf[annotations.FiresEvent]).oneOf()

          outputEventClasses.foreach {
            eventClass =>
              if (method.getReturnType.isAssignableFrom(eventClass))
                throw new common.RecipeValidationException(s"Interaction $name provides event '${eventClass.getName}' that is incompatible with it's return type")
          }
          
          val events: Seq[common.Event] = outputEventClasses.map(eventClassToCommonEvent(_, None))
          common.FiresOneOfEvents(events: _*)
        }
        //ProvidesNothing
        else common.ProvidesNothing
      }
    }
}
