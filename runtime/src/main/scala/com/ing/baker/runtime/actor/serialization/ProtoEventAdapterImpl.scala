package com.ing.baker.runtime.actor.serialization

import com.ing.baker.runtime.actor.serialization.modules._
import scalapb.GeneratedMessage

class ProtoEventAdapterImpl(override val objectSerializer: ObjectSerializer) extends ProtoEventAdapter {

  val registeredModules: Set[ProtoEventAdapterModule] = Set(
    new IntermediateLanguageModule,
    new ProcessIndexModule,
    new RecipeManagerModule,
    new RuntimeModule,
    new TypesModule
  )

  // Combine all partial functions into one partial function
  val toProtoPF: PartialFunction[AnyRef, scalapb.GeneratedMessage] =
    registeredModules
      .map(_.toProto(this))
      .reduce(_ orElse _)

  // Combine all partial functions into one partial function
  val toDomainPF: PartialFunction[scalapb.GeneratedMessage, AnyRef] =
    registeredModules
      .map(_.toDomain(this))
      .reduce(_ orElse _)

  def toProto[T <: scalapb.GeneratedMessage](obj: AnyRef): T = toProtoMessage(obj).asInstanceOf[T]

  def toDomain[T](serializedMessage: scalapb.GeneratedMessage): T = toDomainObject(serializedMessage).asInstanceOf[T]

  def toProtoMessage(obj: AnyRef): scalapb.GeneratedMessage =
    toProtoPF.lift.apply(obj).getOrElse(
      throw new IllegalStateException(s"Cannot serialize object of type ${obj.getClass}"))

  def toDomainObject(serializedMessage: GeneratedMessage): AnyRef =
    toDomainPF.lift.apply(serializedMessage).getOrElse(
      throw new IllegalStateException(s"Unknown protobuf message of type ${serializedMessage.getClass}"))

}
