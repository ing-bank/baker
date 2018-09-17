package com.ing.baker.runtime.actor.serialization.modules

trait ProtoEventAdapterModule {
  def toProto(ctx: ProtoEventAdapterContext): PartialFunction[AnyRef, scalapb.GeneratedMessage]

  def toDomain(ctx: ProtoEventAdapterContext): PartialFunction[scalapb.GeneratedMessage, AnyRef]
}