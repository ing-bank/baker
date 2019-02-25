package com.ing.baker.runtime.actortyped.serialization

import akka.actor.typed.scaladsl.adapter._
import akka.actor.ExtendedActorSystem
import akka.actor.typed.ActorRefResolver
import akka.serialization.{Serialization, SerializationExtension, SerializerWithStringManifest}
import com.ing.baker.runtime.actortyped.recipe_manager.RecipeManagerSerialization
import org.slf4j.LoggerFactory
import com.ing.baker.runtime.actortyped.serialization.protomappings.AnyRefMapping.SerializersProvider

object BakerProtobufSerializer {

  private def entries(implicit ev0: SerializersProvider): List[BinarySerializable] = List(
    new RecipeManagerSerialization.RecipeAddedSerialization
  )

  private val log = LoggerFactory.getLogger(classOf[BakerProtobufSerializer])

  /** Hardcoded serializerId for this serializer. This should not conflict with other serializers.
    * Values from 0 to 40 are reserved for Akka internal usage.
    */
  val identifier = 102
}

class BakerProtobufSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest {

  private val serialization: Serialization = SerializationExtension.get(system)

  private implicit val serializersProvider: SerializersProvider =
    SerializersProvider(
      getSerializerFor = serialization.findSerializerFor,
      serializerByIdentity = serialization.serializerByIdentity.get
    )

  private val actorRefResolver =
    ActorRefResolver(system.toTyped)

  override def identifier: Int =
    BakerProtobufSerializer.identifier

  override def manifest(o: AnyRef): String =
    BakerProtobufSerializer.entries
      .find(_.isInstance(o))
      .map(_.manifest)
      .getOrElse(throw new IllegalStateException(s"Unsupported object of type: ${o.getClass}"))

  override def toBinary(o: AnyRef): Array[Byte] = {
    BakerProtobufSerializer.entries
      .find(_.isInstance(o))
      .map(_.unsafeToBinary(o))
      .getOrElse(throw new IllegalStateException(s"Unsupported object of type: ${o.getClass}"))
  }

  override def fromBinary(bytes: Array[Byte], manifest: String): AnyRef = {
    BakerProtobufSerializer.entries
      .find(_.manifest == manifest)
      .map(_.fromBinaryAnyRef(bytes, actorRefResolver))
      .getOrElse(throw new IllegalStateException(s"Unsupported object with manifest $manifest"))
      .fold(
        { e => BakerProtobufSerializer.log.error(s"Failed to deserialize bytes with manifest $manifest", e); throw e },
        identity
      )
  }
}

