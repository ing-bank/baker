package com.ing.baker.runtime.scaladsl

import com.ing.baker.il.EventDescriptor
import com.ing.baker.runtime.javadsl
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.types.{Converters, NullValue, RecordValue, Value}

import scala.collection.JavaConverters._

case class EventInstance(name: String,
                         providedIngredients: Map[String, Value])
  extends common.EventInstance with ScalaApi {

  def validate(descriptor: EventDescriptor): Seq[String] =
    if (descriptor.name != name)
      Seq(s"Provided event with name '$name' does not match expected name '${descriptor.name}'")
    else
      descriptor.ingredients.flatMap { ingredient =>
        providedIngredients.get(ingredient.name) match {
          case None =>
            Seq(s"no value was provided for ingredient '${ingredient.name}'")
          case Some(NullValue) if !ingredient.`type`.isOption =>
            Seq(s"null is not allowed for non optional ingredient '${ingredient.name}'")
          case Some(value) =>
            value.validate(ingredient.`type`).map(
              reason => s"ingredient '${ingredient.name}' has an incorrect type:\n$reason"
            ).toSeq
          case _ =>
            Seq.empty
        }
      }

  def asJava: javadsl.EventInstance =
    new javadsl.EventInstance(name, providedIngredients.asJava)
}

object EventInstance {
  def apply(name: String): EventInstance =
    new EventInstance(name, Map())

  /**
    * Transforms an object into a RuntimeEvent if possible.
    */
  def unsafeFrom(event: Any): EventInstance = {
    event match {
      case runtimeEvent: EventInstance => runtimeEvent
      case obj =>
        Converters.toValue(obj) match {
          case RecordValue(entries) => new EventInstance(obj.getClass.getSimpleName, entries)
          case other => throw new IllegalArgumentException(s"Unexpected value: $other")
        }
    }
  }
}
