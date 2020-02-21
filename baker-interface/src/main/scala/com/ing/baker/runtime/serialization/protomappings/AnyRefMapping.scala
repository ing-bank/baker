package com.ing.baker.runtime.serialization.protomappings

import akka.serialization.{Serializer, SerializerWithStringManifest}
import com.google.protobuf.ByteString
import com.ing.baker.runtime.serialization.ProtoMap.versioned
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.serialization.{ProtoMap, AkkaSerializerProvider}

import scala.util.{Failure, Success, Try}

class AnyRefMapping(provider: AkkaSerializerProvider) extends ProtoMap[AnyRef, protobuf.SerializedData] {

  val companion = protobuf.SerializedData

  override def toProto(obj: AnyRef): protobuf.SerializedData = {
    val serializer: Serializer = provider.getSerializerFor(obj)
    println(Console.YELLOW + serializer.identifier + " < " + obj + Console.RESET)
    val bytes = provider.encryption.encrypt(serializer.toBinary(obj))
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
      decryptedBytes = provider.encryption.decrypt(bytes.toByteArray)
    } yield
      serializer match {
        case s: SerializerWithStringManifest ⇒ s.fromBinary(decryptedBytes, manifest)
        case _                               ⇒
          val optionalClass = Try { Class.forName(manifest) }.toOption
          serializer.fromBinary(decryptedBytes, optionalClass)
      }

}
