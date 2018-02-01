package com.ing.baker.runtime.actor.serialization

import akka.actor.ExtendedActorSystem
import akka.serialization.{Serializer, SerializerWithStringManifest}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.serialization.ScalaPBSerializer.getManifests
import com.ing.baker.runtime.core
import com.trueaccord.scalapb.{GeneratedMessage, GeneratedMessageCompanion}

class BakerProtobufSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest with DomainProtoTranslation {

  lazy val objectSerializer = new ObjectSerializer(system) {
    // We always use the Kryo serializer for now
     override def getSerializerFor(obj: AnyRef): Serializer = serialization.serializerByIdentity(8675309)
  }

  private val manifests: Map[String, (Class[_ <: AnyRef], GeneratedMessageCompanion[_])] =
    getManifests(system.settings.config.getConfig("baker.scalapb.serialization-manifests"))

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

  def pbTypeForManifest(manifest: String): GeneratedMessageCompanion[_] = manifests.get(manifest) match {
    case None                 => throw new IllegalArgumentException(s"Unkown manifest: $manifest")
    case Some((_, companion)) => companion
  }

  override def toBinary(o: AnyRef): Array[Byte] = toProto(o).toByteArray

  override def fromBinary(bytes: Array[Byte], manifest: String): AnyRef = {

    val protobufType = pbTypeForManifest(manifest)
    val protobuf = protobufType.parseFrom(bytes).asInstanceOf[GeneratedMessage]

    toDomain(protobuf)
  }
}
