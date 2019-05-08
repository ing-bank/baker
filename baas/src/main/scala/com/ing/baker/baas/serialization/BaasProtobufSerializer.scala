package com.ing.baker.baas.serialization

import akka.actor.ExtendedActorSystem
import com.ing.baker.baas.interaction.server.protocol.{ExecuteInteractionHTTPRequest, ExecuteInteractionHTTPResponse}
import com.ing.baker.baas.server.protocol._
import com.ing.baker.runtime.core.actor.serialization.BakerTypedProtobufSerializer.BinarySerializable
import com.ing.baker.runtime.core.actor.serialization.{BakerTypedProtobufSerializer, SerializersProvider}
import org.slf4j.LoggerFactory


object BaasProtobufSerializer {

  private val log = LoggerFactory.getLogger(classOf[BaasProtobufSerializer])

  // Hardcoded serializerId for this serializer. This should not conflict with other serializers.
  // Values from 0 to 40 are reserved for Akka internal usage.
  val identifier = 102

  def entries(implicit ev0: SerializersProvider): List[BinarySerializable] = List(
    BakerTypedProtobufSerializer.forType[AddInteractionHTTPRequest].register,
    BakerTypedProtobufSerializer.forType[AddInteractionHTTPResponse].register,
    BakerTypedProtobufSerializer.forType[AddRecipeRequest].register,
    BakerTypedProtobufSerializer.forType[AddRecipeResponse].register,
    BakerTypedProtobufSerializer.forType[BakeRequest].register,
    BakerTypedProtobufSerializer.forType[BakeResponse].register,
    BakerTypedProtobufSerializer.forType[EventsResponse].register,
    BakerTypedProtobufSerializer.forType[IngredientsResponse].register,
    BakerTypedProtobufSerializer.forType[ProcessEventRequest].register,
    BakerTypedProtobufSerializer.forType[ProcessEventResponse].register,
    BakerTypedProtobufSerializer.forType[StateResponse].register,
    BakerTypedProtobufSerializer.forType[VisualStateResponse].register,
    BakerTypedProtobufSerializer.forType[ExecuteInteractionHTTPRequest].register,
    BakerTypedProtobufSerializer.forType[ExecuteInteractionHTTPResponse].register
  )
}

class BaasProtobufSerializer(system: ExtendedActorSystem) extends BakerTypedProtobufSerializer(system) {

  override lazy val entriesMem: List[BinarySerializable] = BaasProtobufSerializer.entries ++ BakerTypedProtobufSerializer.entries

}
