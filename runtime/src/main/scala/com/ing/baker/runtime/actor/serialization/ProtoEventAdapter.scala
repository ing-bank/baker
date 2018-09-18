package com.ing.baker.runtime.actor.serialization

import com.ing.baker.runtime.actor.serialization.modules._
import scalapb.GeneratedMessage

class ProtoEventAdapter(override val objectSerializer: ObjectSerializer) extends ProtoEventAdapterContext {

  private val registeredModules: Set[ProtoEventAdapterModule] = Set(
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

  def toProtoType[T <: scalapb.GeneratedMessage](obj: AnyRef): T = toProto(obj).asInstanceOf[T]

  def toDomainType[T](serializedMessage: scalapb.GeneratedMessage): T = toDomain(serializedMessage).asInstanceOf[T]

  def toProto(obj: AnyRef): scalapb.GeneratedMessage =
    toProtoPF.lift.apply(obj).getOrElse(
      throw new IllegalStateException(s"Cannot serialize object of type ${obj.getClass}"))

  def toDomain(serializedMessage: GeneratedMessage): AnyRef =
    toDomainPF.lift.apply(serializedMessage).getOrElse(
      throw new IllegalStateException(s"Unknown protobuf message of type ${serializedMessage.getClass}"))

}
