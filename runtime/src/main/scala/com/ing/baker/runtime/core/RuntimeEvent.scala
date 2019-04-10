package com.ing.baker.runtime.core

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.il.EventDescriptor
import com.ing.baker.runtime.actortyped.serialization.BinarySerializable
import com.ing.baker.types.{NullValue, Value}
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping.{toProto, fromProto, versioned}

import scala.collection.JavaConverters._
import scala.util.Try

case class RuntimeEvent(name: String,
                        providedIngredients: Seq[(String, Value)]) {

  /**
    * Returns a scala.collection.immutable.Map of the ingredients provided by this event.
    *
    */
  def providedIngredientsMap: Map[String, Value] = providedIngredients.toMap

  /**
    * Returns a java.util.Map of the ingredients provided by this event.
    *
    * @return a map of the provided ingredients.
    */
  def getProvidedIngredients: java.util.Map[String, Value] = providedIngredientsMap.asJava

  /**
    * This checks if the runtime event is an instance of a event type.
    *
    * @param eventType
    * @return
    */
  def isInstanceOfEventType(eventType: EventDescriptor): Boolean = validateEvent(eventType).isEmpty

  /**
    *
    * Validates the runtime event against a event type and returns a sequence
    * of validation errors.
    *
    * @param eventType The event type to validate against.
    * @return
    */
  def validateEvent(eventType: EventDescriptor): Seq[String] = {

    if (eventType.name != name)
      Seq(s"Provided event with name '$name' does not match expected name '${eventType.name}'")
    else
      // we check all the required ingredient types, additional ones are ignored
      eventType.ingredients.flatMap { ingredient =>
        providedIngredientsMap.get(ingredient.name) match {
          case None        =>
            Seq(s"no value was provided for ingredient '${ingredient.name}'")
          // we can only check the class since the type parameters are available on objects
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
  }
}

object RuntimeEvent {

  def serializer: BinarySerializable =
    new BinarySerializable {

      type Type = RuntimeEvent

      val tag: Class[RuntimeEvent] = classOf[RuntimeEvent]

      def manifest: String = "core.RuntimeEvent"

      def toBinary(a: RuntimeEvent): Array[Byte] = {
        val protoIngredients = a.providedIngredients.map { case (name, value) =>
          protobuf.Ingredient(Some(name), None, Some(toProto(value)))
        }
        protobuf.RuntimeEvent(Some(a.name), protoIngredients).toByteArray
      }

      def fromBinary(binary: Array[Byte]): Try[RuntimeEvent] =
        for {
          message <- Try(protobuf.RuntimeEvent.parseFrom(binary))
          name <- versioned(message.name, "name")
          ingredients <- message.providedIngredients.toList.traverse[Try, (String, Value)] { i =>
            for {
              name <- versioned(i.name, "name")
              protoValue <- versioned(i.value, "value")
              value <- fromProto(protoValue)
            } yield (name, value)
          }
        } yield RuntimeEvent(name, ingredients)
    }
}