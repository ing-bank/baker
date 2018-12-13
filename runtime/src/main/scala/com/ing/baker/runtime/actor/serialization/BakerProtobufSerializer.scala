package com.ing.baker.runtime.actor.serialization

import akka.actor.ExtendedActorSystem
import akka.serialization.{Serialization, SerializationExtension, SerializerWithStringManifest}
import com.ing.baker.il
import com.ing.baker.runtime.actor.process_index.{ProcessIndex, ProcessIndexProtocol}
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.actor.{process_instance, protobuf}
import com.ing.baker.runtime.actor.recipe_manager.{RecipeManager, RecipeManagerProtocol}
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import com.ing.baker.runtime.{actor, core}
import org.slf4j.LoggerFactory
import scalapb.{GeneratedMessage, GeneratedMessageCompanion, Message}

object BakerProtobufSerializer {
  case class Entry[A <: GeneratedMessage with Message[A]](manifest: String, domainClass: Class[_], pbt: GeneratedMessageCompanion[A])

  private val log = LoggerFactory.getLogger(classOf[BakerProtobufSerializer])

  // Hardcoded serializerId for this serializer. This should not conflict with other serializers.
  // Values from 0 to 40 are reserved for Akka internal usage.
  val identifier = 101
}

class BakerProtobufSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest {
  import BakerProtobufSerializer._

  def getSerializationExtension(): Serialization = SerializationExtension.get(system)

  // TODO remove this lazy modifier, but be aware removing lazy causes the tests to hang.
  private lazy val protoEventAdapter = new ProtoEventAdapterImpl(getSerializationExtension(), NoEncryption)

  val manifestInfo = Seq(
    Entry("core.RuntimeEvent", classOf[core.RuntimeEvent], protobuf.RuntimeEvent),
    Entry("core.ProcessState", classOf[core.ProcessState], protobuf.ProcessState),

    Entry("il.CompiledRecipe", classOf[il.CompiledRecipe], protobuf.CompiledRecipe),

    Entry("baker.types.Type", classOf[com.ing.baker.types.Type], actor.protobuf.Type),
    Entry("baker.types.Value", classOf[com.ing.baker.types.Value], actor.protobuf.Value),

    Entry("ProcessIndex.GetShardIndex", classOf[com.ing.baker.runtime.actor.ClusterBakerActorProvider.GetShardIndex], actor.process_index.protobuf.GetShardIndex),

    Entry("ProcessIndex.ActorCreated", classOf[ProcessIndex.ActorCreated], actor.process_index.protobuf.ActorCreated),
    Entry("ProcessIndex.ActorPassivated", classOf[ProcessIndex.ActorPassivated], actor.process_index.protobuf.ActorPassivated),
    Entry("ProcessIndex.ActorActivated", classOf[ProcessIndex.ActorActivated], actor.process_index.protobuf.ActorActivated),
    Entry("ProcessIndex.ActorDeleted", classOf[ProcessIndex.ActorDeleted], actor.process_index.protobuf.ActorDeleted),
    Entry("ProcessIndex.ActorMetadata", classOf[ProcessIndex.ActorMetadata], actor.process_index.protobuf.ActorMetaData),

    Entry("ProcessIndexProtocol.GetIndex", ProcessIndexProtocol.GetIndex.getClass, actor.process_index.protobuf.GetIndex),
    Entry("ProcessIndexProtocol.Index", classOf[ProcessIndexProtocol.Index], actor.process_index.protobuf.Index),
    Entry("ProcessIndexProtocol.CreateProcess", classOf[ProcessIndexProtocol.CreateProcess], actor.process_index.protobuf.CreateProcess),
    Entry("ProcessIndexProtocol.ProcessEvent", classOf[ProcessIndexProtocol.ProcessEvent], actor.process_index.protobuf.ProcessEvent),
    Entry("ProcessIndexProtocol.RetryBlockedInteraction", classOf[ProcessIndexProtocol.RetryBlockedInteraction], actor.process_index.protobuf.RetryBlockedInteraction),
    Entry("ProcessIndexProtocol.ResolveBlockedInteraction", classOf[ProcessIndexProtocol.ResolveBlockedInteraction], actor.process_index.protobuf.ResolveBlockedInteraction),
    Entry("ProcessIndexProtocol.StopRetryingInteraction", classOf[ProcessIndexProtocol.StopRetryingInteraction], actor.process_index.protobuf.StopRetryingInteraction),

    Entry("ProcessIndexProtocol.ProcessEventResponse", classOf[ProcessIndexProtocol.ProcessEventResponse], actor.process_index.protobuf.ProcessEventResponse),
    Entry("ProcessIndexProtocol.GetProcessState", classOf[ProcessIndexProtocol.GetProcessState], actor.process_index.protobuf.GetProcessState),
    Entry("ProcessIndexProtocol.GetCompiledRecipe", classOf[ProcessIndexProtocol.GetCompiledRecipe], actor.process_index.protobuf.GetCompiledRecipe),
    Entry("ProcessIndexProtocol.ReceivePeriodExpired", classOf[ProcessIndexProtocol.ReceivePeriodExpired], actor.process_index.protobuf.ReceivePeriodExpired),
    Entry("ProcessIndexProtocol.InvalidEvent", classOf[ProcessIndexProtocol.InvalidEvent], actor.process_index.protobuf.InvalidEvent),
    Entry("ProcessIndexProtocol.ProcessDeleted", classOf[ProcessIndexProtocol.ProcessDeleted], actor.process_index.protobuf.ProcessDeleted),
    Entry("ProcessIndexProtocol.NoSuchProcess", classOf[ProcessIndexProtocol.NoSuchProcess], actor.process_index.protobuf.NoSuchProcess),
    Entry("ProcessIndexProtocol.ProcessAlreadyExists", classOf[ProcessIndexProtocol.ProcessAlreadyExists], actor.process_index.protobuf.ProcessAlreadyExists),

    Entry("ProcessInstanceProtocol.Stop", classOf[ProcessInstanceProtocol.Stop], actor.process_instance.protobuf.Stop),
    Entry("ProcessInstanceProtocol.GetState", ProcessInstanceProtocol.GetState.getClass, actor.process_instance.protobuf.GetState),
    Entry("ProcessInstanceProtocol.InstanceState", classOf[ProcessInstanceProtocol.InstanceState], actor.process_instance.protobuf.InstanceState),

    Entry("ProcessInstanceProtocol.Initialize", classOf[ProcessInstanceProtocol.Initialize], actor.process_instance.protobuf.Initialize),
    Entry("ProcessInstanceProtocol.Initialized", classOf[ProcessInstanceProtocol.Initialized], actor.process_instance.protobuf.InitializedMessage),
    Entry("ProcessInstanceProtocol.Uninitialized", classOf[ProcessInstanceProtocol.Uninitialized], actor.process_instance.protobuf.Uninitialized),
    Entry("ProcessInstanceProtocol.AlreadyInitialized", classOf[ProcessInstanceProtocol.AlreadyInitialized], actor.process_instance.protobuf.AlreadyInitialized),

    Entry("ProcessInstanceProtocol.FireTransition", classOf[ProcessInstanceProtocol.FireTransition], actor.process_instance.protobuf.FireTransition),
    Entry("ProcessInstanceProtocol.OverrideExceptionStrategy", classOf[ProcessInstanceProtocol.OverrideExceptionStrategy], actor.process_instance.protobuf.OverrideExceptionStrategy),
    Entry("ProcessInstanceProtocol.InvalidCommand", classOf[ProcessInstanceProtocol.InvalidCommand], actor.process_instance.protobuf.InvalidCommand),

    Entry("ProcessInstanceProtocol.AlreadyReceived", classOf[ProcessInstanceProtocol.AlreadyReceived], actor.process_instance.protobuf.AlreadyReceived),
    Entry("ProcessInstanceProtocol.TransitionNotEnabled", classOf[ProcessInstanceProtocol.TransitionNotEnabled], actor.process_instance.protobuf.TransitionNotEnabled),
    Entry("ProcessInstanceProtocol.TransitionFailed", classOf[ProcessInstanceProtocol.TransitionFailed], actor.process_instance.protobuf.TransitionFailedMessage),
    Entry("ProcessInstanceProtocol.TransitionFired", classOf[ProcessInstanceProtocol.TransitionFired], actor.process_instance.protobuf.TransitionFiredMessage),

    Entry("TransitionFired", classOf[process_instance.protobuf.TransitionFired], process_instance.protobuf.TransitionFired),
    Entry("TransitionFailed", classOf[process_instance.protobuf.TransitionFailed], process_instance.protobuf.TransitionFailed),
    Entry("Initialized", classOf[process_instance.protobuf.Initialized], process_instance.protobuf.Initialized),

    Entry("RecipeManager.RecipeAdded", classOf[RecipeManager.RecipeAdded], actor.recipe_manager.protobuf.RecipeAdded),
    Entry("RecipeManagerProtocol.AddRecipe", classOf[RecipeManagerProtocol.AddRecipe], actor.recipe_manager.protobuf.AddRecipe),
    Entry("RecipeManagerProtocol.AddRecipeResponse", classOf[RecipeManagerProtocol.AddRecipeResponse], actor.recipe_manager.protobuf.AddRecipeResponse),
    Entry("RecipeManagerProtocol.GetRecipe", classOf[RecipeManagerProtocol.GetRecipe], actor.recipe_manager.protobuf.GetRecipe),
    Entry("RecipeManagerProtocol.RecipeFound", classOf[RecipeManagerProtocol.RecipeFound], actor.recipe_manager.protobuf.RecipeFound),
    Entry("RecipeManagerProtocol.NoRecipeFound", classOf[RecipeManagerProtocol.NoRecipeFound], actor.recipe_manager.protobuf.NoRecipeFound),
    Entry("RecipeManagerProtocol.GetAllRecipes", RecipeManagerProtocol.GetAllRecipes.getClass, actor.recipe_manager.protobuf.GetAllRecipes),
    Entry("RecipeManagerProtocol.AllRecipes", classOf[RecipeManagerProtocol.AllRecipes], actor.recipe_manager.protobuf.AllRecipes)
  )

  override def identifier: Int = BakerProtobufSerializer.identifier

  override def manifest(o: AnyRef): String = {

    manifestInfo
      .find(_.domainClass.isInstance(o))
      .map(_.manifest)
      .getOrElse(throw new IllegalStateException(s"Unsupported object of type: ${o.getClass}"))
  }

  override def toBinary(o: AnyRef): Array[Byte] = {
    try {
      protoEventAdapter.toProtoMessage(o).toByteArray
    } catch {
      case e: Throwable =>
        log.error(s"Failed to serialize object $o", e)
        throw e;
    }
  }

  override def fromBinary(bytes: Array[Byte], manifest: String): AnyRef = {
    try {
      val pbt = manifestInfo
        .find(_.manifest == manifest)
        .map(_.pbt)
        .getOrElse(throw new IllegalStateException(s"Unknown manifest: $manifest"))

      val protobuf = pbt.parseFrom(bytes).asInstanceOf[GeneratedMessage]

      protoEventAdapter.toDomainObject(protobuf)
    } catch {
      case e: Throwable =>
        log.error(s"Failed to deserialize bytes with manifest $manifest", e)
        throw e;
    }
  }
}
