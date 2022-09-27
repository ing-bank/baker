package com.ing.baker.runtime.akka.actor.serialization

import akka.actor.{ActorRefProvider, ExtendedActorSystem}
import com.ing.baker.il
import com.ing.baker.runtime.akka.actor.ClusterBakerActorProvider
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProto._
import com.ing.baker.runtime.akka.actor.process_index.{ProcessIndex, ProcessIndexProtocol}
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProto._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProto._
import com.ing.baker.runtime.akka.actor.recipe_manager.{RecipeManagerActor, RecipeManagerProtocol}
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata, RecipeInstanceState}
import com.ing.baker.runtime.serialization.ProtoMap
import SerializedDataProto._
import com.ing.baker.runtime.akka.actor.serialization.TypedProtobufSerializer.{BinarySerializable, forType}

object BakerTypedProtobufSerializer {

  def entries(actorRefProvider: ActorRefProvider)(serializersProvider: AkkaSerializerProvider): List[BinarySerializable] = {
    implicit val ev0 = serializersProvider
    implicit val ev1 = actorRefProvider
    commonEntries ++ processIndexEntries ++ processInstanceEntries ++ recipeManagerEntries
  }

  /** Hardcoded serializerId for this serializer. This should not conflict with other serializers.
   * Values from 0 to 40 are reserved for Akka internal usage.
   */
  val identifier = 101

  def commonEntries(implicit ev0: AkkaSerializerProvider): List[BinarySerializable] =
    List(
      forType[com.ing.baker.types.Value]
        .register("baker.types.Value"),
      forType[com.ing.baker.types.Type]
        .register("baker.types.Type"),
      forType[EventInstance]
        .register("core.RuntimeEvent"),
      forType[RecipeInstanceState]
        .register("core.ProcessState"),
      forType[RecipeEventMetadata]
        .register("core.RecipeEventMetadata"),
      forType[il.CompiledRecipe]
        .register("il.CompiledRecipe")
    )

  def processIndexEntries(implicit ev0: AkkaSerializerProvider, actorRefProvider: ActorRefProvider): List[BinarySerializable] =
    List(
      forType[ClusterBakerActorProvider.GetShardIndex]
        .register("ProcessIndex.GetShardIndex"),
      forType[ProcessIndex.ActorCreated]
        .register("ProcessIndex.ActorCreated"),
      forType[ProcessIndex.ActorDeleted]
        .register("ProcessIndex.ActorDeleted"),
      forType[ProcessIndex.ActorPassivated]
        .register("ProcessIndex.ActorPassivated"),
      forType[ProcessIndex.ActorActivated]
        .register("ProcessIndex.ActorActivated"),
      forType[ProcessIndex.ProcessIndexSnapShot]
        .register("ProcessIndex.ProcessIndexSnapShot"),
      forType[ProcessIndex.ActorMetadata]
        .register("ProcessIndex.ActorMetadata"),
      forType[ProcessIndexProtocol.GetIndex.type]
        .register("ProcessIndexProtocol.GetIndex"),
      forType[ProcessIndexProtocol.Index]
        .register("ProcessIndexProtocol.Index"),
      forType[ProcessIndexProtocol.CreateProcess]
        .register("ProcessIndexProtocol.CreateProcess"),
      forType[ProcessIndexProtocol.NoSuchProcess]
        .register("ProcessIndex.NoSuchProcess"),
      forType[ProcessIndexProtocol.ProcessDeleted]
        .register("ProcessIndex.ProcessDeleted"),
      forType[ProcessIndexProtocol.ProcessAlreadyExists]
        .register("ProcessIndex.ProcessAlreadyExists"),
      forType[ProcessIndexProtocol.RetryBlockedInteraction]
        .register("ProcessIndexProtocol.RetryBlockedInteraction"),
      forType[ProcessIndexProtocol.ResolveBlockedInteraction]
        .register("ProcessIndexProtocol.ResolveBlockedInteraction"),
      forType[ProcessIndexProtocol.StopRetryingInteraction]
        .register("ProcessIndexProtocol.StopRetryingInteraction"),
      forType[ProcessIndexProtocol.ProcessEventResponse]
        .register("ProcessIndexProtocol.ProcessEventResponse"),
      forType[ProcessIndexProtocol.GetProcessState]
        .register("ProcessIndexProtocol.GetProcessState"),
      forType[ProcessIndexProtocol.GetCompiledRecipe]
        .register("ProcessIndexProtocol.GetCompiledRecipe"),
      forType[ProcessIndexProtocol.ProcessEvent]
        .register("ProcessIndexProtocol.ProcessEvent"),
      forType[ProcessIndexProtocol.ProcessEventReceivedResponse]
        .register("ProcessIndexProtocol.ProcessEventReceivedResponse"),
      forType[ProcessIndexProtocol.ProcessEventCompletedResponse]
        .register("ProcessIndexProtocol.ProcessEventCompletedResponse"),
      forType[ProcessIndexProtocol.FireSensoryEventRejection.ReceivePeriodExpired]
        .register("ProcessIndexProtocol.FireSensoryEventRejection.ReceivePeriodExpired"),
      forType[ProcessIndexProtocol.FireSensoryEventRejection.InvalidEvent]
        .register("ProcessIndexProtocol.FireSensoryEventRejection.InvalidEvent"),
      forType[ProcessIndexProtocol.FireSensoryEventRejection.RecipeInstanceDeleted]
        .register("ProcessIndexProtocol.FireSensoryEventRejection.RecipeInstanceDeleted"),
      forType[ProcessIndexProtocol.FireSensoryEventRejection.NoSuchRecipeInstance]
        .register("ProcessIndexProtocol.FireSensoryEventRejection.NoSuchProcess"),
      forType[ProcessIndexProtocol.FireSensoryEventRejection.AlreadyReceived]
        .register("ProcessIndexProtocol.FireSensoryEventRejection.AlreadyReceived"),
      forType[ProcessIndexProtocol.FireSensoryEventRejection.FiringLimitMet]
        .register("ProcessIndexProtocol.FireSensoryEventRejection.FiringLimitMet"),
      forType[ProcessIndexProtocol.AddRecipeInstanceMetaData]
      .register("ProcessIndexProtocol.AddRecipeInstanceMetaData")
    )

  def processInstanceEntries(implicit ev0: AkkaSerializerProvider): List[BinarySerializable] =
    List(
      forType[ProcessInstanceProtocol.Stop]
        .register("ProcessInstanceProtocol.Stop"),
      forType[ProcessInstanceProtocol.GetState.type]
        .register("ProcessInstanceProtocol.GetState"),
      forType[ProcessInstanceProtocol.InstanceState]
        .register("ProcessInstanceProtocol.InstanceState"),
      forType[ProcessInstanceProtocol.Initialize]
        .register("ProcessInstanceProtocol.Initialize"),
      forType[ProcessInstanceProtocol.Initialized]
        .register("ProcessInstanceProtocol.Initialized"),
      forType[ProcessInstanceProtocol.Uninitialized]
        .register("ProcessInstanceProtocol.Uninitialized"),
      forType[ProcessInstanceProtocol.AlreadyInitialized]
        .register("ProcessInstanceProtocol.AlreadyInitialized"),
      forType[ProcessInstanceProtocol.FireTransition]
        .register("ProcessInstanceProtocol.FireTransition"),
      forType[ProcessInstanceProtocol.OverrideExceptionStrategy]
        .register("ProcessInstanceProtocol.OverrideExceptionStrategy"),
      forType[ProcessInstanceProtocol.InvalidCommand]
        .register("ProcessInstanceProtocol.InvalidCommand"),
      forType[ProcessInstanceProtocol.AlreadyReceived]
        .register("ProcessInstanceProtocol.AlreadyReceived"),
      forType[ProcessInstanceProtocol.TransitionNotEnabled]
        .register("ProcessInstanceProtocol.TransitionNotEnabled"),
      forType[ProcessInstanceProtocol.TransitionFailed]
        .register("ProcessInstanceProtocol.TransitionFailed"),
      forType[ProcessInstanceProtocol.TransitionFired]
        .register("ProcessInstanceProtocol.TransitionFired"),
      forType[ProcessInstanceProtocol.MetaDataAdded.type]
        .register("ProcessInstanceProtocol.MetaDataAdded"),
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.TransitionFired]
        .register("TransitionFired")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.TransitionFired)),
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.TransitionFailed]
        .register("TransitionFailed")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.TransitionFailed)),
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.Initialized]
        .register("Initialized")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.Initialized)),
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.MetaDataAdded]
        .register("MetaDataAdded")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.MetaDataAdded)),
    )

  def recipeManagerEntries(implicit ev0: AkkaSerializerProvider): List[BinarySerializable] =
    List(
      forType[RecipeManagerProtocol.AddRecipe]
        .register("RecipeManagerProtocol.AddRecipe"),
      forType[RecipeManagerProtocol.AddRecipeResponse]
        .register("RecipeManagerProtocol.AddRecipeResponse"),
      forType[RecipeManagerProtocol.GetRecipe]
        .register("RecipeManagerProtocol.GetRecipe"),
      forType[RecipeManagerProtocol.RecipeFound]
        .register("RecipeManagerProtocol.RecipeFound"),
      forType[RecipeManagerProtocol.NoRecipeFound]
        .register("RecipeManagerProtocol.NoRecipeFound"),
      forType[RecipeManagerProtocol.GetAllRecipes.type]
        .register("RecipeManagerProtocol.GetAllRecipes"),
      forType[RecipeManagerProtocol.AllRecipes]
        .register("RecipeManagerProtocol.AllRecipes"),
      forType[RecipeManagerActor.RecipeAdded]
        .register("RecipeManager.RecipeAdded")
    )
}

class BakerTypedProtobufSerializer(system: ExtendedActorSystem) extends TypedProtobufSerializer(system, BakerTypedProtobufSerializer.identifier, BakerTypedProtobufSerializer.entries(system.provider))
