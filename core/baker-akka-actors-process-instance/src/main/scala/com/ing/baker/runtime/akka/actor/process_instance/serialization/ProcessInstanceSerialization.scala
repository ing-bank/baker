package com.ing.baker.runtime.akka.actor.process_instance.serialization

import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProto._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.akka.actor.serialization.AkkaSerializerProvider
import com.ing.baker.runtime.akka.actor.serialization.SerializedDataProto.akkaAnyRefMapping
import com.ing.baker.runtime.akka.actor.serialization.TypedProtobufSerializer.{BinarySerializable, forType}
import com.ing.baker.runtime.serialization.ProtoMap

/**
 * Provides serialization entries for ProcessInstance actor messages.
 * 
 * This object is responsible for defining how ProcessInstance-related messages
 * are serialized to protobuf format. It owns the serialization logic for all
 * ProcessInstanceProtocol messages.
 */
object ProcessInstanceSerialization {

  /**
   * Returns the list of serialization entries for ProcessInstance messages.
   * 
   * @param serializerProvider Provides access to Akka's serialization system
   * @return List of BinarySerializable entries for ProcessInstance messages
   */
  def entries(implicit serializerProvider: AkkaSerializerProvider): List[BinarySerializable] =
    List(
      forType[ProcessInstanceProtocol.AwaitEvent]
        .register("ProcessInstanceProtocol.AwaitEvent"),
      forType[ProcessInstanceProtocol.EventOccurred.type]
        .register("ProcessInstanceProtocol.EventOccurred"),
      forType[ProcessInstanceProtocol.AwaitCompleted.type]
        .register("ProcessInstanceProtocol.AwaitCompleted"),
      forType[ProcessInstanceProtocol.Completed.type ]
        .register("ProcessInstanceProtocol.Completed"),

      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.CompletionListenerAdded]
        .register("CompletionListenerAdded")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.CompletionListenerAdded)),
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.EventListenerAdded]
        .register("EventListenerAdded")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.EventListenerAdded)),
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.CompletionListenersRemoved]
        .register("CompletionListenersRemoved")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.CompletionListenersRemoved)),
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.EventListenersRemoved]
        .register("EventListenersRemoved")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.EventListenersRemoved)),

      forType[ProcessInstanceProtocol.Stop]
        .register("ProcessInstanceProtocol.Stop"),
      forType[ProcessInstanceProtocol.GetState.type]
        .register("ProcessInstanceProtocol.GetState"),
      forType[ProcessInstanceProtocol.InstanceState]
        .register("ProcessInstanceProtocol.InstanceState"),
      forType[ProcessInstanceProtocol.IngredientFound]
        .register("ProcessInstanceProtocol.IngredientFound"),
      forType[ProcessInstanceProtocol.IngredientNotFound.type]
        .register("ProcessInstanceProtocol.IngredientNotFound"),
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
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.TransitionFailedWithOutput]
        .register("TransitionFailedWithOutput")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.TransitionFailedWithOutput)),
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.TransitionFailedWithFunctionalOutput]
        .register("TransitionFailedWithFunctionalOutput")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.TransitionFailedWithFunctionalOutput)),
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.TransitionFailed]
        .register("TransitionFailed")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.TransitionFailed)),
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.Initialized]
        .register("Initialized")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.Initialized)),
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.MetaDataAdded]
        .register("MetaDataAdded")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.MetaDataAdded)),
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.TransitionDelayed]
        .register("TransitionDelayed")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.TransitionDelayed)),
      forType[com.ing.baker.runtime.akka.actor.process_instance.protobuf.DelayedTransitionFired]
        .register("DelayedTransitionFired")(ProtoMap.identityProtoMap(com.ing.baker.runtime.akka.actor.process_instance.protobuf.DelayedTransitionFired)),
    )
}
