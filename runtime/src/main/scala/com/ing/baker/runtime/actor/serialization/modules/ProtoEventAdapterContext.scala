package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.runtime.actor.serialization.ObjectSerializer
import scalapb.GeneratedMessage

trait ProtoEventAdapterContext {

  val objectSerializer: ObjectSerializer

  def toProtoType[T <: scalapb.GeneratedMessage](obj: AnyRef): T

  def toDomainType[T](serializedMessage: scalapb.GeneratedMessage): T

  implicit class MsgOptionOps[T <: GeneratedMessage](option: Option[T]) {
    def mapToDomain[B]: Option[B] = option.map(e => toDomainType[B](e))
  }
}
