package com.ing.baker.runtime.actor.serialization

import akka.actor.ExtendedActorSystem
import akka.serialization.SerializerWithStringManifest
import com.ing.baker.il
import com.ing.baker.runtime.actor.ClusterBakerActorProvider.GetShardIndex
import com.ing.baker.runtime.actor.process_index.ProcessIndex._
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.actor.process_index.ProcessIndexProto._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProto._
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProto._
import com.ing.baker.runtime.actor.serialization.BakerTypedProtobufSerializer.BinarySerializable
import org.slf4j.LoggerFactory
import com.ing.baker.runtime.core.{BakerResponseEventProtocol, ProcessState, RuntimeEvent}

import scala.reflect.ClassTag
import scala.util.Try

object BakerTypedProtobufSerializer {

  private val log = LoggerFactory.getLogger(classOf[BakerTypedProtobufSerializer])

  /** Hardcoded serializerId for this serializer. This should not conflict with other serializers.
    * Values from 0 to 40 are reserved for Akka internal usage.
    */
  val identifier = 101

  def entries(implicit ev0: SerializersProvider): List[BinarySerializable] = List(

    forType[com.ing.baker.types.Value].register("baker.types.Value"),
    forType[com.ing.baker.types.Type].register("baker.types.Type"),

    forType[BakerResponseEventProtocol].register("com.ing.baker.runtime.core.BakerResponseEventProtocol"),
    forType[RuntimeEvent].register("core.RuntimeEvent"),
    forType[ProcessState].register("core.ProcessState"),

    forType[il.CompiledRecipe].register("il.CompiledRecipe"),

    forType[GetShardIndex].register("ProcessIndex.GetShardIndex"),
    forType[ActorCreated].register("ProcessIndex.ActorCreated"),
    forType[ActorDeleted].register("ProcessIndex.ActorDeleted"),
    forType[ActorPassivated].register("ProcessIndex.ActorPassivated"),
    forType[ActorActivated].register("ProcessIndex.ActorActivated"),
    forType[ActorMetadata].register("ProcessIndex.ActorMetadata"),

    forType[GetIndex.type].register("ProcessIndexProtocol.GetIndex"),

    forType[Index].register("ProcessIndexProtocol.Index"),
    forType[CreateProcess].register("ProcessIndexProtocol.CreateProcess"),
    forType[ProcessEvent].register("ProcessIndexProtocol.ProcessEvent"),
    forType[RetryBlockedInteraction].register("ProcessIndexProtocol.RetryBlockedInteraction"),
    forType[ResolveBlockedInteraction].register("ProcessIndexProtocol.ResolveBlockedInteraction"),
    forType[StopRetryingInteraction].register("ProcessIndexProtocol.StopRetryingInteraction"),

    forType[ProcessEventResponse].register("ProcessIndexProtocol.ProcessEventResponse"),
    forType[GetProcessState].register("ProcessIndexProtocol.GetProcessState"),
    forType[GetCompiledRecipe].register("ProcessIndexProtocol.GetCompiledRecipe"),
    forType[ReceivePeriodExpired].register("ProcessIndexProtocol.ReceivePeriodExpired"),
    forType[InvalidEvent].register("ProcessIndexProtocol.InvalidEvent"),
    forType[ProcessDeleted].register("ProcessIndexProtocol.ProcessDeleted"),
    forType[NoSuchProcess].register("ProcessIndexProtocol.NoSuchProcess"),
    forType[ProcessAlreadyExists].register("ProcessIndexProtocol.ProcessAlreadyExists"),

    forType[ProcessInstanceProtocol.Stop].register("ProcessInstanceProtocol.Stop"),
    forType[ProcessInstanceProtocol.GetState.type].register("ProcessInstanceProtocol.GetState"),
    forType[ProcessInstanceProtocol.InstanceState].register("ProcessInstanceProtocol.InstanceState"),

    forType[ProcessInstanceProtocol.Initialize].register("ProcessInstanceProtocol.Initialize"),
    forType[ProcessInstanceProtocol.Initialized].register("ProcessInstanceProtocol.Initialized"),
    forType[ProcessInstanceProtocol.Uninitialized].register("ProcessInstanceProtocol.Uninitialized"),
    forType[ProcessInstanceProtocol.AlreadyInitialized].register("ProcessInstanceProtocol.AlreadyInitialized"),

    forType[ProcessInstanceProtocol.FireTransition].register("ProcessInstanceProtocol.FireTransition"),
    forType[ProcessInstanceProtocol.OverrideExceptionStrategy].register("ProcessInstanceProtocol.OverrideExceptionStrategy"),
    forType[ProcessInstanceProtocol.InvalidCommand].register("ProcessInstanceProtocol.InvalidCommand"),

    forType[ProcessInstanceProtocol.AlreadyReceived].register("ProcessInstanceProtocol.AlreadyReceived"),
    forType[ProcessInstanceProtocol.TransitionNotEnabled].register("ProcessInstanceProtocol.TransitionNotEnabled"),
    forType[ProcessInstanceProtocol.TransitionFailed].register("ProcessInstanceProtocol.TransitionFailed"),
    forType[ProcessInstanceProtocol.TransitionFired].register("ProcessInstanceProtocol.TransitionFired"),

    forType[com.ing.baker.runtime.actor.process_instance.protobuf.TransitionFired].register("TransitionFired")(ProtoMap.identityProtoMap(com.ing.baker.runtime.actor.process_instance.protobuf.TransitionFired)),
    forType[com.ing.baker.runtime.actor.process_instance.protobuf.TransitionFailed].register("TransitionFailed")(ProtoMap.identityProtoMap(com.ing.baker.runtime.actor.process_instance.protobuf.TransitionFailed)),
    forType[com.ing.baker.runtime.actor.process_instance.protobuf.Initialized].register("Initialized")(ProtoMap.identityProtoMap(com.ing.baker.runtime.actor.process_instance.protobuf.Initialized)),

    forType[AddRecipe].register("RecipeManagerProtocol.AddRecipe"),
    forType[AddRecipeResponse].register("RecipeManagerProtocol.AddRecipeResponse"),
    forType[GetRecipe].register("RecipeManagerProtocol.GetRecipe"),
    forType[RecipeFound].register("RecipeManagerProtocol.RecipeFound"),
    forType[NoRecipeFound].register("RecipeManagerProtocol.NoRecipeFound"),
    forType[GetAllRecipes.type].register("RecipeManagerProtocol.GetAllRecipes"),
    forType[AllRecipes].register("RecipeManagerProtocol.AllRecipes"),

    forType[RecipeAdded].register("RecipeManager.RecipeAdded")
  )

  def forType[A <: AnyRef](implicit tag: ClassTag[A]): RegisterFor[A] = new RegisterFor[A](tag)

  class RegisterFor[A <: AnyRef](classTag: ClassTag[A]) {

    def register[P <: scalapb.GeneratedMessage with scalapb.Message[P]](implicit protoMap: ProtoMap[A, P]): BinarySerializable =
      register[P](None)

    def register[P <: scalapb.GeneratedMessage with scalapb.Message[P]](overrideName: String)(implicit protoMap: ProtoMap[A, P]): BinarySerializable =
      register[P](Some(overrideName))

    def register[P <: scalapb.GeneratedMessage with scalapb.Message[P]](overrideName: Option[String])(implicit protoMap: ProtoMap[A, P]): BinarySerializable = {
      new BinarySerializable {

        override type Type = A

        override val tag: Class[_] = classTag.runtimeClass

        override val manifest: String = overrideName.getOrElse(classTag.runtimeClass.getName)

        override def toBinary(a: Type): Array[Byte] = protoMap.toByteArray(a)

        override def fromBinary(binary: Array[Byte]): Try[Type] = protoMap.fromByteArray(binary)
      }
    }
  }

  trait BinarySerializable {

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

  implicit def serializersProvider: SerializersProvider = SerializersProvider(system)

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

