package com.ing.baker.runtime.akka.actor.serialization

import akka.actor.{ActorRefProvider, ExtendedActorSystem}
import com.ing.baker.il
import com.ing.baker.runtime.akka.actor.serialization.TypedProtobufSerializer.{BinarySerializable, forType}
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata, RecipeInstanceState}
import com.ing.baker.runtime.akka.actor.process_index.serialization.ProcessIndexSerialization
import com.ing.baker.runtime.akka.actor.process_instance.serialization.ProcessInstanceSerialization
import com.ing.baker.runtime.akka.actor.recipe_manager.serialization.RecipeManagerSerialization
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.serialization.DelayedTransitionSerialization

/**
 * Main serializer for all Baker actor messages.
 * 
 * This serializer acts as a proxy that delegates to module-specific serialization
 * providers while maintaining a single serializer ID (101) for backward compatibility
 * with persisted events in the journal.
 * 
 * Architecture:
 * - Common entries (shared types) defined locally
 * - Actor-specific entries delegated to their respective modules:
 *   - ProcessIndexSerialization (process-index module)
 *   - ProcessInstanceSerialization (process-instance module)
 *   - RecipeManagerSerialization (recipe-manager module)
 *   - DelayedTransitionSerialization (delayed-transition module)
 */
object BakerTypedProtobufSerializer {

  /**
   * Aggregates all serialization entries from common types and actor modules.
   * 
   * @param actorRefProvider Provides actor reference resolution capabilities
   * @param serializersProvider Provides access to Akka's serialization system
   * @return Complete list of all serialization entries for Baker
   */
  def entries(actorRefProvider: ActorRefProvider)(serializersProvider: AkkaSerializerProvider): List[BinarySerializable] = {
    implicit val ev0 = serializersProvider
    implicit val ev1 = actorRefProvider
    
    // Aggregate entries from all modules
    commonEntries ++
    ProcessIndexSerialization.entries ++
    ProcessInstanceSerialization.entries ++
    RecipeManagerSerialization.entries ++
    DelayedTransitionSerialization.entries
  }

  /** Hardcoded serializerId for this serializer. This should not conflict with other serializers.
   * Values from 0 to 40 are reserved for Akka internal usage.
   */
  val identifier = 101

  /**
   * Common serialization entries for shared Baker types.
   * 
   * These types are used across multiple actor modules and are defined here
   * in the integration module for convenience.
   */
  private def commonEntries(implicit ev0: AkkaSerializerProvider): List[BinarySerializable] =
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
}

/**
 * Akka serializer implementation that extends TypedProtobufSerializer.
 *
 * This class is instantiated by Akka during actor system initialization based
 * on the configuration in reference.conf.
 */
class BakerTypedProtobufSerializer(system: ExtendedActorSystem) extends TypedProtobufSerializer(system, BakerTypedProtobufSerializer.identifier, BakerTypedProtobufSerializer.entries(system.provider))
