package com.ing.baker.runtime.actortyped.serialization

import akka.actor.typed.ActorRefResolver

import scala.util.Try

trait BinarySerializable {

  type Type <: AnyRef

  val tag: Class[Type]

  def manifest: String

  def toBinary(a: Type): Array[Byte]

  def fromBinary(binary: Array[Byte], resolver: ActorRefResolver): Try[Type]

  def isInstance(o: AnyRef): Boolean =
    tag.isInstance(o)

  def unsafeToBinary(a: AnyRef): Array[Byte] =
    toBinary(a.asInstanceOf[Type])

  def fromBinaryAnyRef(binary: Array[Byte], resolver: ActorRefResolver): Try[AnyRef] =
    fromBinary(binary, resolver)

}
