package com.ing.baker.runtime.akka.actor.serialization

import akka.actor.ActorRef
import com.ing.baker.il
import com.ing.baker.types
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.akka.actor.serialization.protomappings._
import com.ing.baker.runtime.common.BakerException
import com.ing.baker.runtime.scaladsl.{EventInstance, EventMoment, IngredientInstance, RecipeInformation, RecipeInstanceMetadata, RecipeInstanceState, SensoryEventResult}
import scalapb.GeneratedMessageCompanion

import scala.util.{Success, Try}

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

  implicit def anyRefMapping(implicit ev0: SerializersProvider): ProtoMap[AnyRef, protobuf.SerializedData] =
    new AnyRefMapping(ev0)

  implicit def compiledRecipeMapping(implicit ev0: ProtoMap[AnyRef, protobuf.SerializedData]): ProtoMap[il.CompiledRecipe, protobuf.CompiledRecipe] =
    new CompiledRecipeMapping(ev0)

  implicit def akkaActorRefMapping(implicit ev0: SerializersProvider): ProtoMap[ActorRef, protobuf.ActorRefId] =
    new ActorRefMapping(ev0)

  implicit def recipeInformationMapping(implicit ev0: SerializersProvider): ProtoMap[RecipeInformation, protobuf.RecipeInformation] =
    new RecipeInformationMapping()

  implicit val bakerExceptionMapping: ProtoMap[BakerException, protobuf.BakerException] =
    new BakerExceptionMapping

  implicit val eventDescriptorMapping: ProtoMap[il.EventDescriptor, protobuf.EventDescriptor] =
    new EventDescriptorMapping

  implicit val ingredientDescriptorMapping: ProtoMap[il.IngredientDescriptor, protobuf.IngredientDescriptor] =
    new IngredientDescriptorMapping

  implicit val ingredientInstanceMapping: ProtoMap[IngredientInstance, protobuf.Ingredient] =
    new IngredientInstanceMapping

  implicit val bakerTypeMapping: ProtoMap[types.Type, protobuf.Type] =
    new BakerTypesMapping

  implicit val bakerValueMapping: ProtoMap[types.Value, protobuf.Value] =
    new BakerValuesMapping

  implicit val interactionFailureStrategyMapping: ProtoMap[il.failurestrategy.InteractionFailureStrategy, protobuf.InteractionFailureStrategy] =
    new InteractionFailureStrategyMapping

  implicit val eventOutputTransformerMapping: ProtoMap[il.EventOutputTransformer, protobuf.EventOutputTransformer] =
    new EventOutputTransformerMapping

  implicit val runtimeEventMapping: ProtoMap[EventInstance, protobuf.RuntimeEvent] =
    new RuntimeEventMapping

  implicit val recipeInstanceMetadataMapping: ProtoMap[RecipeInstanceMetadata, protobuf.RecipeInstanceMetadata] =
    new RecipeInstanceMetadataMapping

  implicit val processStateMapping: ProtoMap[RecipeInstanceState, protobuf.ProcessState] =
    new ProcessStateMapping

  implicit val eventMomentMapping: ProtoMap[EventMoment, protobuf.EventMoment] =
    new EventMomentMapping

  implicit val processEventResult: ProtoMap[SensoryEventResult, protobuf.SensoryEventResult] =
    new SensoryEventResultMapping

  def identityProtoMap[A <: scalapb.GeneratedMessage with scalapb.Message[A]](companion0: GeneratedMessageCompanion[A]): ProtoMap[A, A] =
    new ProtoMap[A, A] {

      override def companion: GeneratedMessageCompanion[A] = companion0

      override def toProto(a: A): A = a

      override def fromProto(message: A): Try[A] = Success(message)
    }
}
