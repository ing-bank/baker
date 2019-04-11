package com.ing.baker.runtime.actortyped.serialization

import akka.actor.ExtendedActorSystem
import akka.serialization.{Serialization, SerializationExtension, SerializerWithStringManifest}
import com.ing.baker.runtime.actor.process_index.ProcessIndexSerialization
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerSerialization._
import org.slf4j.LoggerFactory
import com.ing.baker.runtime.actortyped.serialization.protomappings.AnyRefMapping.SerializersProvider
import com.ing.baker.runtime.core.{ProcessState, RuntimeEvent}

import scala.reflect.ClassTag
import scala.util.Try

object BakerTypedProtobufSerializer {

  private val log = LoggerFactory.getLogger(classOf[BakerTypedProtobufSerializer])

  /** Hardcoded serializerId for this serializer. This should not conflict with other serializers.
    * Values from 0 to 40 are reserved for Akka internal usage.
    */
  val identifier = 103

  private def entries(implicit ev0: SerializersProvider): List[BinarySerializable] = List(
    forType[RuntimeEvent].register,
    forType[ProcessState].register,

    ProcessIndexSerialization.getShardIndex,
    ProcessIndexSerialization.actorCreated,
    ProcessIndexSerialization.actorDeleted,
    ProcessIndexSerialization.actorPassivated,
    ProcessIndexSerialization.actorActivated,
    ProcessIndexSerialization.getIndex,
    ProcessIndexSerialization.index,
    ProcessIndexSerialization.createProcess,
    ProcessIndexSerialization.processEvent,
    ProcessIndexSerialization.retryBlockedInteraction,
    ProcessIndexSerialization.resolveBlockedInteraction,
    ProcessIndexSerialization.stopRetryingInteraction,
    ProcessIndexSerialization.actorMetadata,

    forType[AddRecipe].register,
    forType[AddRecipeResponse].register,
    forType[GetRecipe].register,
    forType[RecipeFound].register,
    forType[NoRecipeFound].register,
    forType[GetAllRecipes.type].register,
    forType[AllRecipes].register,
    forType[RecipeAdded].register
  )

  private def forType[A <: AnyRef](implicit tag: ClassTag[A]): RegisterFor[A] = new RegisterFor[A](tag)

  private class RegisterFor[A <: AnyRef](classTag: ClassTag[A]) {

    def register[P <: scalapb.GeneratedMessage with scalapb.Message[P]](implicit protoMap: ProtoMap[A, P]): BinarySerializable = {
      new BinarySerializable {

        override type Type = A

        override val tag: Class[_] = classTag.runtimeClass

        override def manifest: String = classTag.runtimeClass.getPackage.getName + "." + classTag.runtimeClass.getName

        override def toBinary(a: Type): Array[Byte] = protoMap.toByteArray(a)

        override def fromBinary(binary: Array[Byte]): Try[Type] = protoMap.fromByteArray(binary)
      }
    }
  }

}

class BakerTypedProtobufSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest {

  private implicit def serializersProvider: SerializersProvider = {
    val serialization: Serialization = SerializationExtension.get(system)
    SerializersProvider(
      getSerializerFor = serialization.findSerializerFor,
      serializerByIdentity = serialization.serializerByIdentity.get
    )
  }

  lazy val entriesMem: List[BinarySerializable] = BakerTypedProtobufSerializer.entries

  override def identifier: Int =
    BakerTypedProtobufSerializer.identifier

  override def manifest(o: AnyRef): String = {
    entriesMem
      .find(_.isInstance(o))
      .map(_.manifest)
      .getOrElse(throw new IllegalStateException(s"Unsupported object of type: ${o.getClass}"))
  }

  override def toBinary(o: AnyRef): Array[Byte] =
    entriesMem
      .find(_.isInstance(o))
      .map(_.unsafeToBinary(o))
      .getOrElse(throw new IllegalStateException(s"Unsupported object of type: ${o.getClass}"))

  override def fromBinary(bytes: Array[Byte], manifest: String): AnyRef =
    entriesMem
      .find(_.manifest == manifest)
      .map(_.fromBinaryAnyRef(bytes))
      .getOrElse(throw new IllegalStateException(s"Unsupported object with manifest $manifest"))
      .fold(
        { e => BakerTypedProtobufSerializer.log.error(s"Failed to deserialize bytes with manifest $manifest", e); throw e },
        identity
      )
}

