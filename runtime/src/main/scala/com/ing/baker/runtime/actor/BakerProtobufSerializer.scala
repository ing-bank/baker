package com.ing.baker.runtime.actor

import akka.actor.ExtendedActorSystem
import akka.serialization.SerializerWithStringManifest
import com.ing.baker.petrinet.akka.AkkaObjectSerializer
import com.ing.baker.runtime.actor.messages.Ingredient
import com.ing.baker.runtime.core
import com.ing.baker.serialization._

class BakerProtobufSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest {

  lazy val objectSerializer = new AkkaObjectSerializer(system)

  override def identifier: Int = 123

  override def manifest(o: AnyRef): String = {
    o match {
      case e: core.RuntimeEvent => "RuntimeEvent"
      case e: core.ProcessState => "ProcessState"
    }
  }

  def writeIngredients(ingredients: Map[String, Any]): Seq[messages.Ingredient] = {
    ingredients.map { case (name, value) =>

      val serializedObject = objectSerializer.serializeObject(value.asInstanceOf[AnyRef])
      val objectMessage = transformToProto(serializedObject)

      messages.Ingredient(Some(name), Some(objectMessage))
    }.toSeq
  }

  def readIngredients(ingredients: Seq[Ingredient]): Map[String, Any] = {
    ingredients.map {
      case messages.Ingredient(Some(name), Some(data)) =>

        val deserializedData = transformFromProto(data)
        val deserializedObject = objectSerializer.deserializeObject(deserializedData)
        name -> deserializedObject
    }.toMap
  }

  override def toBinary(o: AnyRef): Array[Byte] = {
    // translate domain model to protobuf
    o match {
      case e: core.RuntimeEvent =>
        val ingredients = writeIngredients(e.ingredients)
        val eventMessage = messages.RuntimeEvent(Some(e.name), ingredients)
        messages.RuntimeEvent.toByteArray(eventMessage)

      case e: core.ProcessState =>
        val ingredients = writeIngredients(e.ingredients)
        val processsStateMesage = messages.ProcessState(Some(e.processId), ingredients)
        messages.ProcessState.toByteArray(processsStateMesage)
    }
  }

  override def fromBinary(bytes: Array[Byte], manifest: String): AnyRef = {

    // translate from protobuf to domain model
    manifest match {
      case "RuntimeEvent" =>
        val eventMessage = messages.RuntimeEvent.parseFrom(bytes)
        eventMessage match {
          case messages.RuntimeEvent(Some(name), ingredients) => core.RuntimeEvent(name, readIngredients(ingredients))
          case _ => throw new IllegalStateException(s"Failed to deserialize RuntimeEvent message (missing 'name' field)")
        }
      case "ProcessState" =>
        val eventMessage = messages.ProcessState.parseFrom(bytes)
        eventMessage match {
          case messages.ProcessState(Some(id), ingredients) => core.ProcessState(id, readIngredients(ingredients))
          case _ => throw new IllegalStateException(s"Failed to deserialize ProcessState message (missing 'id' field)")
        }
    }
  }
}
