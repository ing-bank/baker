package com.ing.baker.runtime.actor.serialization

import com.ing.baker.runtime.actor.serialization.modules._
import scalapb.GeneratedMessage

trait ProtoEventAdapter extends ProtoEventAdapterContext {

  private val registeredModules: Set[ProtoEventAdapterModule] = Set(
    new IntermediateLanguageModule,
    new ProcessIndexModule,
    new RecipeManagerModule,
    new RuntimeModule,
    new TypesModule
  )

  def toProtoType[T <: scalapb.GeneratedMessage](obj: AnyRef): T = toProto(obj).asInstanceOf[T]

  def toDomainType[T](serializedMessage: scalapb.GeneratedMessage): T = toDomain(serializedMessage).asInstanceOf[T]

  def toProto(obj: AnyRef): scalapb.GeneratedMessage = {
    registeredModules.map(_.toProto(this)) // extract the partial function to apply
      .reduce[PartialFunction[AnyRef, scalapb.GeneratedMessage]] { case (f1, f2) => f1 orElse f2 } // Combine all partial functions into one partial function
      .lift.apply(obj).getOrElse(throw new IllegalStateException(s"Cannot serialize object of type ${obj.getClass}"))
  }

  def toDomain(serializedMessage: GeneratedMessage): AnyRef = {
    registeredModules.map(_.toDomain(this)) // extract the partial function to apply
      .reduce[PartialFunction[scalapb.GeneratedMessage,AnyRef]] { case (f1, f2) => f1 orElse f2 } // Combine all partial functions into one partial function
      .lift.apply(serializedMessage).getOrElse(throw new IllegalStateException(s"Unknown protobuf message of type ${serializedMessage.getClass}"))
  }

}
