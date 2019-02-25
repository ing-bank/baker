package com.ing.baker.runtime.actortyped.serialization.protomappings

import com.google.protobuf.ByteString
import akka.serialization.{Serializer, SerializerWithStringManifest}
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping.versioned
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actortyped.serialization.protomappings.AnyRefMapping.SerializersProvider

import scala.util.{Failure, Success, Try}

object AnyRefMapping {

  case class SerializersProvider(getSerializerFor: AnyRef => Serializer, serializerByIdentity: Int => Option[Serializer])
}

class AnyRefMapping(provider: SerializersProvider) extends ProtobufMapping[AnyRef] {

  override type ProtoClass = protobuf.SerializedData

  override def toProto(obj: AnyRef): protobuf.SerializedData = {
    val serializer: Serializer = provider.getSerializerFor(obj)
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

  override def fromProto(message: protobuf.SerializedData): Try[AnyRef] =
    for {
      serializerId <- versioned(message.serializerId, "serializerId")
      manifest <- versioned(message.manifest, "manifest")
      bytes <- versioned(message.data, "data")
      serializer <- provider.serializerByIdentity(serializerId) match {
        case Some(serializer) => Success(serializer)
        case None => Failure(new IllegalStateException(s"No serializer found with id $serializerId"))
      }
    } yield
      serializer match {
        case s: SerializerWithStringManifest ⇒ s.fromBinary(bytes.toByteArray, manifest)
        case _                               ⇒
          val optionalClass = Try { Class.forName(manifest) }.toOption
          serializer.fromBinary(bytes.toByteArray, optionalClass)
      }

}
