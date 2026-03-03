package com.ing.baker.runtime

import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction}
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance, InteractionInstanceInput}
import com.ing.baker.types.Converters.toJava
import com.ing.baker.types.{Converters, Type, Value}

import scala.concurrent.Future
import scala.reflect.runtime.universe.TypeTag

/**
  *  This class is for wiring the scala DSL to the runtime components (interaction implementations).
  *
  */
object ScalaDSLRuntime {

  def ScalaInteractionImplementation(i: Interaction, fn: Seq[IngredientInstance] => EventInstance): InteractionInstance = {
    InteractionInstance(
      name = i.name,
      input = i.inputIngredients.map(i => InteractionInstanceInput(Some(i.name), i.ingredientType)),
      output = None,
      run = input => Future.successful(Some(fn(input)))
    )
  }

  // TODO use shapeless to abstract over function arity and add type safety
  implicit class InteractionOps(i: Interaction) {

    def implement[A : TypeTag](fn: A => EventInstance): InteractionInstance =
      ScalaInteractionImplementation(i, { input =>
        fn(toJava[A](input.head.value))
      })

    def implement[A : TypeTag, B : TypeTag](fn: (A, B) => EventInstance): InteractionInstance =
      ScalaInteractionImplementation(i, { input =>
        fn(toJava[A](input.head.value), toJava[B](input(1).value))
      })

    def implement[A : TypeTag, B : TypeTag, C : TypeTag](fn: (A, B, C) => EventInstance): InteractionInstance =
      ScalaInteractionImplementation(i, { input =>
        fn(toJava[A](input.head.value), toJava[B](input(1).value), toJava[C](input(2).value))
      })
  }

  implicit class EventOps(e: Event) {
    def instance(values: Any*): EventInstance = {

      val providedIngredients: Map[String, Value] =
        e.providedIngredients.map(_.name).zip(values.toSeq.map(Converters.toValue)).toMap

      EventInstance(e.name, providedIngredients)
    }
  }

  implicit object IngredientMap {

    def apply(values: (Ingredient[_], Any)*): Map[String, Value] = {
      values.map { case (key, value) => key.name -> Converters.toValue(value)
      }.toMap
    }
  }
}
