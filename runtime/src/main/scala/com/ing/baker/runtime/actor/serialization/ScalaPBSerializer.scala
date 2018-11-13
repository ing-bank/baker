package com.ing.baker.runtime.actor.serialization

import akka.actor.ExtendedActorSystem
import akka.serialization.{SerializationExtension, SerializerWithStringManifest}

/**
  * This serializer was used in Baker 1.3.x for ProcessInstance events
  *
  * It is kept for backwards compatibility but just forwards to BakerProtobufSerializer
  */
@Deprecated
class ScalaPBSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest {

  private lazy val protobufSerializer = SerializationExtension.get(system).serializerByIdentity(101).asInstanceOf[BakerProtobufSerializer]

  // Hardcoded serializerId for this serializer. This should not conflict with other serializers.
  // Values from 0 to 40 are reserved for Akka internal usage.
  override def identifier: Int = 102

  override def fromBinary(bytes: Array[Byte], manifest: String): AnyRef = protobufSerializer.fromBinary(bytes, manifest)

  override def manifest(o: AnyRef): String = protobufSerializer.manifest(o)

  override def toBinary(o: AnyRef): Array[Byte] = protobufSerializer.toBinary(o)
}