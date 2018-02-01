package com.ing.baker.runtime.actor.serialization

import akka.actor.ActorSystem
import akka.serialization.{SerializationExtension, Serializer, SerializerWithStringManifest}
import com.google.protobuf.ByteString
import com.ing.baker.runtime.actor.messages.SerializedData
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption

class ObjectSerializer(system: ActorSystem, encryption: Encryption = NoEncryption) {

  val serialization = SerializationExtension.get(system)

  def getSerializerFor(obj: AnyRef): Serializer = serialization.findSerializerFor(obj)

  def serializeObject(obj: AnyRef): SerializedData = {
    val serializer: Serializer = getSerializerFor(obj)
    val bytes = encryption.encrypt(serializer.toBinary(obj))

    val manifest = serializer match {
      case s: SerializerWithStringManifest ⇒ s.manifest(obj)
      case _                               ⇒ if (obj != null) obj.getClass.getName else ""
    }

    // we should not have to copy the bytes
    SerializedData(
      serializerId = Some(serializer.identifier),
      manifest = Some(manifest),
      data = Some(ByteString.copyFrom(bytes))
    )
  }

  def deserializeObject(data: SerializedData): AnyRef = {
    data match {
      case SerializedData(Some(serializerId), Some(manifest), Some(bytes)) ⇒

        val serializer = serialization.serializerByIdentity.getOrElse(serializerId,
          throw new IllegalStateException(s"No serializer found with id $serializerId")
        )

        val decryptedBytes = encryption.decrypt(bytes.toByteArray)

        serializer match {
          case s: SerializerWithStringManifest ⇒ s.fromBinary(decryptedBytes, manifest)
          case _                               ⇒ serializer.fromBinary(decryptedBytes, Class.forName(manifest))
        }

      case _ => throw new IllegalArgumentException("Missing data in protobuf message")
    }
  }
}

