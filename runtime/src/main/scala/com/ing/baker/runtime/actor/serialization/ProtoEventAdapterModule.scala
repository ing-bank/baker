package com.ing.baker.runtime.actor.serialization

/**
  * A module that can translate to/from protobuf for a particular domain.
  */
trait ProtoEventAdapterModule {

  /**
    * Translates the given object to it's protobuf counter part.
    */
  def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage]

  /**
    * Translates the given protobuf message to a domain object.
    */
  def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef]
}