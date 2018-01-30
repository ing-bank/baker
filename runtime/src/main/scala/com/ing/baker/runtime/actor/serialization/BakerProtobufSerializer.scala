package com.ing.baker.runtime.actor.serialization

import java.util.concurrent.TimeUnit

import akka.actor.ExtendedActorSystem
import akka.serialization.{Serializer, SerializerWithStringManifest}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.types.Value
import com.ing.baker.runtime.actor.messages
import com.ing.baker.runtime.core

import scala.concurrent.duration.Duration

class BakerProtobufSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest {

  lazy val objectSerializer = new ObjectSerializer(system) {
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
      case _: CompiledRecipe    => "CompiledRecipe"
    }
  }

  def writeIngredients(ingredients: Seq[(String, Value)]): Seq[messages.Ingredient] = {
    ingredients.map { case (name, value) =>
      val serializedObject = objectSerializer.serializeObject(value)
      val objectMessage = serializedObject.toProto
      messages.Ingredient(Some(name), Some(objectMessage))
    }
  }

  def readIngredients(ingredients: Seq[messages.Ingredient]): Seq[(String, Value)] = {
    ingredients.map {
      case messages.Ingredient(Some(name), Some(data)) =>
        val deserializedData = data.toDomain
        val deserializedObject = objectSerializer.deserializeObject(deserializedData).asInstanceOf[Value]
        name -> deserializedObject
      case _ => throw new IllegalArgumentException("Missing fields in Protobuf data when deserializing ingredients")
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

      case CompiledRecipe(name, petriNet, initialMarking, sensoryEvents, validationErrors, eventReceivePeriod, retentionPeriod) =>

        val eventReceiveMillis = eventReceivePeriod.map(_.toMillis)
        val retentionMillis = retentionPeriod.map(_.toMillis)

//        messages.CompiledRecipe(Some(name), petriNet, sensoryEvents, validationErrors, eventReceiveMillis, retentionMillis)
        null
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
      case "CompiledRecipe" =>

        val compiledRecipeMessage = messages.CompiledRecipe.parseFrom(bytes)
        compiledRecipeMessage match {
          case messages.CompiledRecipe(Some(name), Some(petrinet), sensoryEvents, validationErrors, eventReceiveMillis, retentionMillis) =>

            val eventReceivePeriod = eventReceiveMillis.map(Duration(_, TimeUnit.MILLISECONDS))
            val retentionPeriod = retentionMillis.map(Duration(_, TimeUnit.MILLISECONDS))

//            CompiledRecipe(name, petrinet, initialMarking, sensoryEvents, validationErrors, eventReceivePeriod, retentionPeriod)

            null
        }
    }
  }
}
