package com.ing.baker.runtime.actortyped.serialization

import com.ing.baker.il
import com.ing.baker.types
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actortyped.serialization.protomappings.AnyRefMapping.SerializersProvider
import com.ing.baker.runtime.actortyped.serialization.protomappings._
import com.ing.baker.runtime.core.RuntimeEvent
import scalapb.GeneratedMessageCompanion

import scala.util.Try

trait ProtoMap[A, P <: scalapb.GeneratedMessage with scalapb.Message[P]] {

  def companion: GeneratedMessageCompanion[P]

  def toProto(a: A): P

  def fromProto(message: P): Try[A]

  def toByteArray(a: A): Array[Byte] =
    toProto(a).toByteArray

  def fromByteArray(binary: Array[Byte]): Try[A] =
    Try(companion.parseFrom(binary)).flatMap(fromProto)

}

object ProtoMap {

  def ctxToProto[A, P <: scalapb.GeneratedMessage with scalapb.Message[P]](a: A)(implicit ev: ProtoMap[A, P]): P = ev.toProto(a)

  def ctxFromProto[A, P <: scalapb.GeneratedMessage with scalapb.Message[P]](proto: P)(implicit ev: ProtoMap[A, P]): Try[A] = ev.fromProto(proto)

  def versioned[A](a: Option[A], name: String): Try[A] =
    Try(a.getOrElse(throw new IllegalStateException(s"Missing field '$name' from protobuf message, probably we recieved a different version of the message")))

  implicit def anyRefMapping(implicit provider: SerializersProvider): ProtoMap[AnyRef, protobuf.SerializedData] =
    new AnyRefMapping(provider)

  implicit def compiledRecipeMapping(implicit ev0: ProtoMap[AnyRef, protobuf.SerializedData]): ProtoMap[il.CompiledRecipe, protobuf.CompiledRecipe] =
    new CompiledRecipeMapping(ev0)

  implicit val eventDescriptorMapping: ProtoMap[il.EventDescriptor, protobuf.EventDescriptor] =
    new EventDescriptorMapping

  implicit val ingredientDescriptorMapping: ProtoMap[il.IngredientDescriptor, protobuf.IngredientDescriptor] =
    new IngredientDescriptorMapping

  implicit val bakerTypeMapping: ProtoMap[types.Type, protobuf.Type] =
    new BakerTypesMapping

  implicit val bakerValueMapping: ProtoMap[types.Value, protobuf.Value] =
    new BakerValuesMapping

  implicit val interactionFailureStrategyMapping: ProtoMap[il.failurestrategy.InteractionFailureStrategy, protobuf.InteractionFailureStrategy] =
    new InteractionFailureStrategyMapping

  implicit val eventOutputTransformerMapping: ProtoMap[il.EventOutputTransformer, protobuf.EventOutputTransformer] =
    new EventOutputTransformerMapping

  implicit val runtimeEventMapping: ProtoMap[RuntimeEvent, protobuf.RuntimeEvent] =
    new RuntimeEventMapping
}
