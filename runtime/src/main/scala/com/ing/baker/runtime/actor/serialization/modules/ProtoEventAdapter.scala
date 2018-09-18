package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.runtime.actor.serialization.ObjectSerializer

/**
  * Responsible to translate to/from protobuf messages.
  */
trait ProtoEventAdapter {

  val objectSerializer: ObjectSerializer

  def toProto[T <: scalapb.GeneratedMessage](obj: AnyRef): T

  def toDomain[T](serializedMessage: scalapb.GeneratedMessage): T
}
