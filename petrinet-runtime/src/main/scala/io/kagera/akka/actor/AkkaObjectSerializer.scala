package io.kagera.akka.actor

import akka.actor.ActorSystem
import akka.serialization.{ SerializationExtension, SerializerWithStringManifest }
import io.kagera.runtime.persistence.Encryption.NoEncryption
import io.kagera.runtime.persistence.{ ObjectSerializer, SerializedObject }
import io.kagera.runtime.persistence.{ Encryption, ObjectSerializer, SerializedObject }

class AkkaObjectSerializer(system: ActorSystem, encryption: Encryption = NoEncryption) extends ObjectSerializer {

  private val serialization = SerializationExtension.get(system)

  override def serializeObject(obj: AnyRef): SerializedObject = {
    // for now we re-use akka Serialization extension for pluggable serializers
    val serializer = serialization.findSerializerFor(obj)
    val bytes = encryption.encrypt(serializer.toBinary(obj))

    val manifest = serializer match {
      case s: SerializerWithStringManifest ⇒ s.manifest(obj)
      case _                               ⇒ if (obj != null) obj.getClass.getName else ""
    }

    // we should not have to copy the bytes
    SerializedObject(
      serializerId = serializer.identifier,
      manifest = manifest,
      bytes = bytes
    )
  }

  override def deserializeObject(data: SerializedObject): AnyRef = {
    data match {
      case SerializedObject(serializerId, manifest, bytes) ⇒

        val serializer = serialization.serializerByIdentity.getOrElse(serializerId,
          throw new IllegalStateException(s"No serializer found with id $serializerId")
        )

        val decryptedBytes = encryption.decrypt(bytes)

        serializer match {
          case s: SerializerWithStringManifest ⇒ s.fromBinary(decryptedBytes, manifest)
          case _                               ⇒ serializer.fromBinary(decryptedBytes, Class.forName(manifest))
        }
    }
  }
}

