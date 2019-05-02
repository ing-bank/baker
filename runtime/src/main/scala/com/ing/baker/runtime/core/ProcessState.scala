package com.ing.baker.runtime.core

import com.ing.baker.types.PrimitiveValue
import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.types.Value
import com.ing.baker.runtime.actor.{ protobuf => proto }
import com.ing.baker.runtime.actor.serialization.ProtoMap
import com.ing.baker.runtime.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}

import scala.collection.JavaConverters._
import scala.util.Try

/**
  * Holds the 'state' of a process instance.
  *
  * @param processId   The process identifier
  * @param ingredients The accumulated ingredients
  * @param eventNames  The names of the events occurred so far
  */
case class ProcessState(processId: String,
                        ingredients: Map[String, Value],
                        eventNames: List[String]) extends Serializable {

  /**
    * Returns the accumulated ingredients.
    *
    * @return The accumulated ingredients
    */
  def getIngredients(): java.util.Map[String, Value] = ingredients.asJava

  /**
    * Returns the names of the events occurred so far.
    *
    * @return The names of the events occurred so far
    */
  def getEventNames(): java.util.List[String] = eventNames.asJava

  /**
    * Returns the process identifier.
    *
    * @return The process identifier
    */
  def getProcessId(): String = processId


  def filterIngredients(ingredientFilter: Seq[String]): ProcessState =
    copy(processId,
      ingredients.map(ingredient =>
        if (ingredientFilter.contains(ingredient._1))
          ingredient._1 -> PrimitiveValue("")
        else
          ingredient
      ), eventNames)

}

object ProcessState {

  implicit def protoMap: ProtoMap[ProcessState, proto.ProcessState] =
    new ProtoMap[ProcessState, proto.ProcessState] {

      val companion = proto.ProcessState

      def toProto(a: ProcessState): proto.ProcessState = {
        val protoIngredients = a.ingredients.toSeq.map { case (name, value) =>
          proto.Ingredient(Some(name), None, Some(ctxToProto(value)))
        }
        proto.ProcessState(Some(a.processId), protoIngredients, a.eventNames)
      }

      def fromProto(message: proto.ProcessState): Try[ProcessState] =
        for {
          processId <- versioned(message.processId, "processId")
          ingredients <- message.ingredients.toList.traverse[Try, (String, Value)] { i =>
            for {
              name <- versioned(i.name, "name")
              protoValue <- versioned(i.value, "value")
              value <- ctxFromProto(protoValue)
            } yield (name, value)
          }
        } yield ProcessState(processId, ingredients.toMap, message.eventNames.toList)
    }
}