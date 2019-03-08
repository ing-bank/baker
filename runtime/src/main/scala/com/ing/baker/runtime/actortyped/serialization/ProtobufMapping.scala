package com.ing.baker.runtime.actortyped.serialization

import com.ing.baker.il
import com.ing.baker.types
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actortyped.serialization.protomappings.AnyRefMapping.SerializersProvider
import com.ing.baker.runtime.actortyped.serialization.protomappings._

import scala.util.Try

trait ProtobufMapping[A, P] {

  def toProto(a: A): P

  def fromProto(message: P): Try[A]

}

object ProtobufMapping {

  def toProto[A, P](a: A)(implicit ev: ProtobufMapping[A, P]): P = ev.toProto(a)

  def fromProto[A, P](proto: P)(implicit ev: ProtobufMapping[A, P]): Try[A] = ev.fromProto(proto)

  def versioned[A](a: Option[A], name: String): Try[A] =
    Try(a.getOrElse(throw new IllegalStateException(s"Missing field '$name' from protobuf message, probably we recieved a different version of the message")))

  implicit def anyRefMapping(implicit provider: SerializersProvider): ProtobufMapping[AnyRef, protobuf.SerializedData] =
    new AnyRefMapping(provider)

  implicit def compiledRecipeMapping(implicit ev0: ProtobufMapping[AnyRef, protobuf.SerializedData]): ProtobufMapping[il.CompiledRecipe, protobuf.CompiledRecipe] =
    new CompiledRecipeMapping(ev0)

  implicit val eventDescriptorMapping: ProtobufMapping[il.EventDescriptor, protobuf.EventDescriptor] =
    new EventDescriptorMapping

  implicit val ingredientDescriptorMapping: ProtobufMapping[il.IngredientDescriptor, protobuf.IngredientDescriptor] =
    new IngredientDescriptorMapping

  implicit val bakerTypeMapping: ProtobufMapping[types.Type, protobuf.Type] =
    new BakerTypesMapping

  implicit val bakerValueMapping: ProtobufMapping[types.Value, protobuf.Value] =
    new BakerValuesMapping

  implicit val interactionFailureStrategyMapping: ProtobufMapping[il.failurestrategy.InteractionFailureStrategy, protobuf.InteractionFailureStrategy] =
    new InteractionFailureStrategyMapping

  implicit val eventOutputTransformerMapping: ProtobufMapping[il.EventOutputTransformer, protobuf.EventOutputTransformer] =
    new EventOutputTransformerMapping
}
