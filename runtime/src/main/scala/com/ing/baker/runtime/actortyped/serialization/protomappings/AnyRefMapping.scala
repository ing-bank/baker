package com.ing.baker.runtime.actortyped.serialization.protomappings

import com.google.protobuf.ByteString
import akka.serialization.{Serializer, SerializerWithStringManifest}
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actortyped.serialization.protomappings.AnyRefMapping.GetSerializerFor

import scala.util.Try

object AnyRefMapping {

  case class GetSerializerFor(run: AnyRef => Serializer) extends AnyVal

}

class AnyRefMapping(getSerializerFor: GetSerializerFor) extends ProtobufMapping[AnyRef] {

  override type ProtoClass = protobuf.SerializedData

  override def toProto(obj: AnyRef): protobuf.SerializedData = {
    val serializer: Serializer = getSerializerFor.run(obj)
    val bytes = serializer.toBinary(obj)
    val manifest = serializer match {
      case s: SerializerWithStringManifest ⇒ s.manifest(obj)
      case _                               ⇒ if (obj != null) obj.getClass.getName else ""
    }
    protobuf.SerializedData(
      serializerId = Some(serializer.identifier),
      manifest = Some(manifest),
      data = Some(ByteString.copyFrom(bytes))
    )
  }

  override def fromProto(message: protobuf.SerializedData): Try[AnyRef] = ???
}
