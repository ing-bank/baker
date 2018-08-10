package com.ing.baker.recipe

import java.lang.reflect.Method

import com.ing.baker.recipe.javadsl.ReflectionHelpers._
import com.ing.baker.types.{Converters, Type}

package object javadsl {

  private val interactionMethodName: String = "apply"

  def createIngredient(ingredientName: String, ingredientType: Type): common.Ingredient =
    new common.Ingredient(
      name = ingredientName,
      ingredientType = ingredientType
    )

  def parseType(javaType: java.lang.reflect.Type, errorMessage: String): Type = {
    try {
      Converters.readJavaType(javaType)
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

  def interactionClassToCommonInteraction(interactionClass: Class[_ <: Interaction], newName: Option[String]): InteractionDescriptor = {

    val name: String = interactionClass.getSimpleName

    val method: Method = interactionClass.getDeclaredMethods
      .find(_.getName == interactionMethodName)
      .getOrElse(throw new IllegalStateException(
        s"No method named '$interactionMethodName' defined on '${interactionClass.getName}'"))

    val inputIngredients: Seq[common.Ingredient] =
      method.getParameterNames.map(name =>
        createIngredient(name,
          parseType(
            method.parameterTypeForName(name).get,
            s"Unsupported type for ingredient '$name' on interaction '${interactionClass.getName}'")))

    val output: common.InteractionOutput = {
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
            if (!method.getReturnType.isAssignableFrom(eventClass))
              throw new common.RecipeValidationException(s"Interaction $name provides event '${eventClass.getName}' that is incompatible with it's return type")
        }

        val events: Seq[common.Event] = outputEventClasses.map(eventClassToCommonEvent(_, None))
        common.FiresOneOfEvents(events: _*)
      }
      //ProvidesNothing
      else common.ProvidesNothing
    }

    InteractionDescriptor(name, inputIngredients, output, Set.empty, Set.empty, Map.empty, Map.empty, None, None, None, Map.empty, newName)
  }
}
