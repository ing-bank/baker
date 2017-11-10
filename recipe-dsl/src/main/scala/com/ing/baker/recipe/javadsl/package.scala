package com.ing.baker.recipe

import java.lang.reflect.{Method, Type}

import com.ing.baker.recipe.javadsl.ReflectionHelpers._
import com.ing.baker.types.Converters

package object javadsl {

  def createIngredient(ingredientName: String, ingredientClazz: Type): common.Ingredient =
    new common.Ingredient(
      name = ingredientName,
      ingredientType = Converters.readJavaType(ingredientClazz)
  )


  def eventClassToCommonEvent(eventClass: Class[_], firingLimit: Option[Integer]): common.Event =
    new common.Event {
      override val name: String = eventClass.getSimpleName
      override val providedIngredients: Seq[common.Ingredient] =
        eventClass.getDeclaredFields
          .filter(field => !field.isSynthetic)
          .map(f => createIngredient(f.getName, f.getGenericType))
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

      override val inputIngredients: Seq[common.Ingredient] = method.getParameterNames.map(s => createIngredient(s, method.parameterTypeForName(s).get))

      override val output: common.InteractionOutput = {
        if(method.isAnnotationPresent(classOf[annotations.ProvidesIngredient]) && method.isAnnotationPresent(classOf[annotations.FiresEvent]))
          throw new common.RecipeValidationException(s"Interaction $name has both ProvidesIngredient and FiresEvent annotation, only one if possible")
        //ProvidesIngredient
        else if (method.isAnnotationPresent(classOf[annotations.ProvidesIngredient])) {
          val interactionOutputName: String = method.getAnnotation(classOf[annotations.ProvidesIngredient]).value()
          common.ProvidesIngredient(createIngredient(interactionOutputName, method.getGenericReturnType))
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
