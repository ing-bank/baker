package com.ing.baker.runtime.actor.serialization

import com.ing.baker.runtime.actor.protobuf.SerializedData

/**
  * Responsible to translate to/from protobuf messages.
  */
trait ProtoEventAdapter {

  def toProtoAny(obj: AnyRef): SerializedData

  def toProto[T <: scalapb.GeneratedMessage](obj: AnyRef): T

  def toDomain[T](serializedMessage: scalapb.GeneratedMessage): T
}
