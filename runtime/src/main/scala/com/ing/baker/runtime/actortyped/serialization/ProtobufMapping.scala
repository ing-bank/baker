package com.ing.baker.runtime.actortyped.serialization

import com.ing.baker.il
import com.ing.baker.types
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actortyped.serialization.protomappings.AnyRefMapping.SerializersProvider
import com.ing.baker.runtime.actortyped.serialization.protomappings._

import scala.util.Try

trait ProtobufMapping[A] {

  type ProtoClass

  def toProto(a: A): ProtoClass

  def fromProto(message: ProtoClass): Try[A]

}

object ProtobufMapping {

  type Aux[A, P] = ProtobufMapping[A] { type ProtoClass = P }

  def toProto[A, P](a: A)(implicit ev: Aux[A, P]): P = ev.toProto(a)

  def fromProto[A, P](proto: P)(implicit ev: Aux[A, P]): Try[A] = ev.fromProto(proto)

  def versioned[A](a: Option[A], name: String): Try[A] =
    Try(a.getOrElse(throw new IllegalStateException(s"Missing field '$name' from protobuf message, probably we recieved a different version of the message")))

  implicit def anyRefMapping(implicit provider: SerializersProvider): Aux[AnyRef, protobuf.SerializedData] =
    new AnyRefMapping(provider)

  implicit def compiledRecipeMapping(implicit ev0: Aux[AnyRef, protobuf.SerializedData]): Aux[il.CompiledRecipe, protobuf.CompiledRecipe] =
    new CompiledRecipeMapping(ev0)

  implicit val eventDescriptorMapping: Aux[il.EventDescriptor, protobuf.EventDescriptor] =
    new EventDescriptorMapping

  implicit val ingredientDescriptorMapping: Aux[il.IngredientDescriptor, protobuf.IngredientDescriptor] =
    new IngredientDescriptorMapping

  implicit val bakerTypeMapping: Aux[types.Type, protobuf.Type] =
    new BakerTypesMapping

  implicit val bakerValueMapping: Aux[types.Value, protobuf.Value] =
    new BakerValuesMapping

  implicit val interactionFailureStrategyMapping: Aux[il.failurestrategy.InteractionFailureStrategy, protobuf.InteractionFailureStrategy] =
    new InteractionFailureStrategyMapping

  implicit val eventOutputTransformerMapping: Aux[il.EventOutputTransformer, protobuf.EventOutputTransformer] =
    new EventOutputTransformerMapping
}
