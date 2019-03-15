package com.ing.baker.runtime.actortyped.serialization

import akka.actor.typed.scaladsl.adapter._
import akka.actor.ExtendedActorSystem
import akka.actor.typed.ActorRefResolver
import akka.serialization.{Serialization, SerializationExtension, SerializerWithStringManifest}
import com.ing.baker.runtime.actortyped.recipe_manager.RecipeManagerSerialization
import org.slf4j.LoggerFactory
import com.ing.baker.runtime.actortyped.serialization.protomappings.AnyRefMapping.SerializersProvider

object BakerTypedProtobufSerializer {

  private def entries(implicit ev0: SerializersProvider): List[BinarySerializable] = List(
    new RecipeManagerSerialization.RecipeAddedSerialization
  )

  private val log = LoggerFactory.getLogger(classOf[BakerTypedProtobufSerializer])

  /** Hardcoded serializerId for this serializer. This should not conflict with other serializers.
    * Values from 0 to 40 are reserved for Akka internal usage.
    */
  val identifier = 103
}

class BakerTypedProtobufSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest {

  private implicit def serializersProvider: SerializersProvider = {
    val serialization: Serialization = SerializationExtension.get(system)
    SerializersProvider(
      getSerializerFor = serialization.findSerializerFor,
      serializerByIdentity = serialization.serializerByIdentity.get
    )
  }

  private lazy val actorRefResolver =
    ActorRefResolver(system.toTyped)

  override def identifier: Int =
    BakerTypedProtobufSerializer.identifier

  override def manifest(o: AnyRef): String = {
    BakerTypedProtobufSerializer.entries
      .find(_.isInstance(o))
      .map(_.manifest)
      .getOrElse(throw new IllegalStateException(s"Unsupported object of type: ${o.getClass}"))
  }

  override def toBinary(o: AnyRef): Array[Byte] = {
    BakerTypedProtobufSerializer.entries
      .find(_.isInstance(o))
      .map(_.unsafeToBinary(o))
      .getOrElse(throw new IllegalStateException(s"Unsupported object of type: ${o.getClass}"))
  }

  override def fromBinary(bytes: Array[Byte], manifest: String): AnyRef = {
    BakerTypedProtobufSerializer.entries
      .find(_.manifest == manifest)
      .map(_.fromBinaryAnyRef(bytes, actorRefResolver))
      .getOrElse(throw new IllegalStateException(s"Unsupported object with manifest $manifest"))
      .fold(
        { e => BakerTypedProtobufSerializer.log.error(s"Failed to deserialize bytes with manifest $manifest", e); throw e },
        identity
      )
  }
}

