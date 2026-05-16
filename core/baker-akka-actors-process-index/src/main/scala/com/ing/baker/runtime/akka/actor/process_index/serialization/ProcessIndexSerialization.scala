package com.ing.baker.runtime.akka.actor.process_index.serialization

import akka.actor.ActorRefProvider
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProto._
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol
import com.ing.baker.runtime.akka.actor.serialization.AkkaSerializerProvider
import com.ing.baker.runtime.akka.actor.serialization.SerializedDataProto.akkaAnyRefMapping
import com.ing.baker.runtime.akka.actor.serialization.TypedProtobufSerializer.{BinarySerializable, forType}

/**
 * Provides serialization entries for ProcessIndex actor messages.
 * 
 * This object is responsible for defining how ProcessIndex-related messages
 * are serialized to protobuf format. It owns the serialization logic for all
 * ProcessIndexProtocol messages.
 */
object ProcessIndexSerialization {

  /**
   * Returns the list of serialization entries for ProcessIndex messages.
   * 
   * Note: ProcessIndex serialization requires ActorRefProvider for handling
   * actor references in certain message types.
   * 
   * @param serializerProvider Provides access to Akka's serialization system
   * @param actorRefProvider Provides actor reference resolution capabilities
   * @return List of BinarySerializable entries for ProcessIndex messages
   */
  def entries(implicit serializerProvider: AkkaSerializerProvider, actorRefProvider: ActorRefProvider): List[BinarySerializable] =
    List(
      forType[ProcessIndexProtocol.GetShardIndex]
        .register("ProcessIndex.GetShardIndex"),
      forType[ProcessIndexProtocol.ActorCreated]
        .register("ProcessIndex.ActorCreated"),
      forType[ProcessIndexProtocol.ActorDeleted]
        .register("ProcessIndex.ActorDeleted"),
      forType[ProcessIndexProtocol.ActorPassivated]
        .register("ProcessIndex.ActorPassivated"),
      forType[ProcessIndexProtocol.ActorActivated]
        .register("ProcessIndex.ActorActivated"),
      forType[ProcessIndexProtocol.ProcessIndexSnapShot]
        .register("ProcessIndex.ProcessIndexSnapShot"),
      forType[ProcessIndexProtocol.ActorMetadata]
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
      forType[ProcessIndexProtocol.HasRecipeInstance]
        .register("ProcessIndexProtocol.HasRecipeInstance"),
      forType[ProcessIndexProtocol.RecipeInstanceExists]
        .register("ProcessIndexProtocol.RecipeInstanceExists"),
      forType[ProcessIndexProtocol.GetProcessState]
        .register("ProcessIndexProtocol.GetProcessState"),
      forType[ProcessIndexProtocol.DeleteProcess]
        .register("ProcessIndexProtocol.DeleteProcess"),
      forType[ProcessIndexProtocol.GetProcessIngredient]
        .register("ProcessIndexProtocol.GetProcessIngredientc"),
      forType[ProcessIndexProtocol.GetCompiledRecipe]
        .register("ProcessIndexProtocol.GetCompiledRecipe"),
      forType[ProcessIndexProtocol.ProcessEvent]
        .register("ProcessIndexProtocol.ProcessEvent"),
      forType[ProcessIndexProtocol.ProcessSensoryEvent]
        .register("ProcessIndexProtocol.ProcessSensoryEvent"),
      forType[ProcessIndexProtocol.AwaitCompleted]
        .register("ProcessIndexProtocol.AwaitCompleted"),
      forType[ProcessIndexProtocol.AwaitEvent]
        .register("ProcessIndexProtocol.AwaitEvent"),
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
}
