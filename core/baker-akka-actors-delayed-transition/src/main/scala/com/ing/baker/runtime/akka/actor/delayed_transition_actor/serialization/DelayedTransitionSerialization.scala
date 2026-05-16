package com.ing.baker.runtime.akka.actor.delayed_transition_actor.serialization

import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionActorProtocol
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionProto._
import com.ing.baker.runtime.akka.actor.serialization.AkkaSerializerProvider
import com.ing.baker.runtime.akka.actor.serialization.TypedProtobufSerializer.{BinarySerializable, forType}

/**
 * Provides serialization entries for DelayedTransitionActor messages.
 * 
 * This object is responsible for defining how DelayedTransitionActor-related messages
 * are serialized to protobuf format. It owns the serialization logic for all
 * DelayedTransitionActorProtocol messages.
 */
object DelayedTransitionSerialization {

  /**
   * Returns the list of serialization entries for DelayedTransitionActor messages.
   * 
   * @param serializerProvider Provides access to Akka's serialization system
   * @return List of BinarySerializable entries for DelayedTransitionActor messages
   */
  def entries(implicit serializerProvider: AkkaSerializerProvider): List[BinarySerializable] =
    List(
      forType[DelayedTransitionActorProtocol.DelayedTransitionInstance]
        .register("DelayedTransitionInstance"),
      forType[DelayedTransitionActorProtocol.DelayedTransitionScheduled]
        .register("DelayedTransitionScheduled"),
      forType[DelayedTransitionActorProtocol.DelayedTransitionExecuted]
        .register("DelayedTransitionExecuted"),
      forType[DelayedTransitionActorProtocol.DelayedTransitionSnapshot]
        .register("DelayedTransitionSnapshot")
    )
}
