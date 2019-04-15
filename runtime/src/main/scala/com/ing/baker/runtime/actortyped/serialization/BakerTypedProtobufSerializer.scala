package com.ing.baker.runtime.actortyped.serialization

import akka.actor.ExtendedActorSystem
import akka.serialization.{Serialization, SerializationExtension, SerializerWithStringManifest}
import com.ing.baker.runtime.actor.ClusterBakerActorProvider.GetShardIndex
import com.ing.baker.runtime.actor.process_index.ProcessIndex._
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.actor.process_index.ProcessIndexProto._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProto._
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProto._
import com.ing.baker.runtime.actortyped.serialization.BakerTypedProtobufSerializer.BinarySerializable
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

  private[serialization] def entries(implicit ev0: SerializersProvider): List[BinarySerializable] = List(
    forType[RuntimeEvent].register,
    forType[ProcessState].register,

    forType[GetShardIndex].register,
    forType[ActorCreated].register,
    forType[ActorDeleted].register,
    forType[ActorPassivated].register,
    forType[ActorActivated].register,

    forType[GetIndex.type].register,

    forType[Index].register,
    forType[CreateProcess].register,
    forType[ProcessEvent].register,
    forType[RetryBlockedInteraction].register,
    forType[ResolveBlockedInteraction].register,
    forType[StopRetryingInteraction].register,
    forType[ActorMetadata].register,

    forType[ProcessEventResponse].register,
    forType[GetProcessState].register,
    forType[GetCompiledRecipe].register,
    forType[ReceivePeriodExpired].register,
    forType[InvalidEvent].register,
    forType[ProcessDeleted].register,
    forType[NoSuchProcess].register,
    forType[ProcessAlreadyExists].register,

    forType[ProcessInstanceProtocol.Stop].register,
    forType[ProcessInstanceProtocol.GetState.type].register,
    forType[ProcessInstanceProtocol.InstanceState].register,

    forType[AddRecipe].register,
    forType[AddRecipeResponse].register,
    forType[GetRecipe].register,
    forType[RecipeFound].register,
    forType[NoRecipeFound].register,
    forType[GetAllRecipes.type].register,
    forType[AllRecipes].register,
    forType[RecipeAdded].register
  )

  private[serialization] def forType[A <: AnyRef](implicit tag: ClassTag[A]): RegisterFor[A] = new RegisterFor[A](tag)

  private[serialization] class RegisterFor[A <: AnyRef](classTag: ClassTag[A]) {

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

  private[serialization] trait BinarySerializable {

    type Type <: AnyRef

    val tag: Class[_]

    def manifest: String

    def toBinary(a: Type): Array[Byte]

    // The actor resolver is commented for future Akka Typed implementation
    def fromBinary(binary: Array[Byte]/*, resolver: ActorRefResolver*/): Try[Type]

    def isInstance(o: AnyRef): Boolean =
      tag.isInstance(o)

    def unsafeToBinary(a: AnyRef): Array[Byte] =
      toBinary(a.asInstanceOf[Type])

    // The actor resolver is commented for future Akka Typed implementation
    def fromBinaryAnyRef(binary: Array[Byte]/*, resolver: ActorRefResolver*/): Try[AnyRef] =
      fromBinary(binary)

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

