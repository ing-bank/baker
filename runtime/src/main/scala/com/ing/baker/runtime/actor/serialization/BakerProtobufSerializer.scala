package com.ing.baker.runtime.actor.serialization

import akka.actor.ExtendedActorSystem
import akka.serialization.{Serializer, SerializerWithStringManifest}
import com.ing.baker.runtime.actor.messages
import com.ing.baker.runtime.core

class BakerProtobufSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest {

  lazy val objectSerializer = new AkkaObjectSerializer(system) {
    // We always use the Kryo serializer for now
     override def getSerializerFor(obj: AnyRef): Serializer = serialization.serializerByIdentity(8675309)
  }

  // Hardcoded serializerId for this serializer. This should not conflict with other serializers.
  // Values from 0 to 40 are reserved for Akka internal usage.
  override def identifier: Int = 101

  override def manifest(o: AnyRef): String = {
    o match {
      case _: core.RuntimeEvent => "RuntimeEvent"
      case _: core.ProcessState => "ProcessState"
    }
  }

  def writeIngredients(ingredients: Seq[(String, Any)]): Seq[messages.Ingredient] = {
    ingredients.map { case (name, value) =>
      val serializedObject = objectSerializer.serializeObject(value.asInstanceOf[AnyRef])
      val objectMessage = transformToProto(serializedObject)
      messages.Ingredient(Some(name), Some(objectMessage))
    }
  }

  def readIngredients(ingredients: Seq[messages.Ingredient]): Seq[(String, Any)] = {
    ingredients.map {
      case messages.Ingredient(Some(name), Some(data)) =>

        val deserializedData = transformFromProto(data)
        val deserializedObject = objectSerializer.deserializeObject(deserializedData)
        name -> deserializedObject
    }
  }

  override def toBinary(o: AnyRef): Array[Byte] = {
    // translate domain model to protobuf
    o match {
      case e: core.RuntimeEvent =>
        val ingredients = writeIngredients(e.providedIngredients)
        val eventMessage = messages.RuntimeEvent(Some(e.name), ingredients)
        messages.RuntimeEvent.toByteArray(eventMessage)

      case e: core.ProcessState =>
        val ingredients = writeIngredients(e.ingredients.toSeq)
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
          case messages.ProcessState(Some(id), ingredients) => core.ProcessState(id, readIngredients(ingredients).toMap)
          case _ => throw new IllegalStateException(s"Failed to deserialize ProcessState message (missing 'id' field)")
        }
    }
  }
}
