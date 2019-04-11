package com.ing.baker.runtime.actortyped.serialization

import scala.util.Try

trait BinarySerializable {

  type Type <: AnyRef

  val tag: Class[_]

  def manifest: String

  def toBinary(a: Type): Array[Byte]

  // The actor resolver is commented for future Akka Typed implementation
  def fromBinary(binary: Array[Byte]/*, resolver: ActorRefResolver*/): Try[Type]

  def isInstance(o: AnyRef): Boolean =
    tag.isInstance(o)

  def unsafeToBinary(a: AnyRef): Array[Byte] =
    toBinary(a.asInstanceOf[Type])

  // The actor resolver is commented for future Akka Typed implementation
  def fromBinaryAnyRef(binary: Array[Byte]/*, resolver: ActorRefResolver*/): Try[AnyRef] =
    fromBinary(binary)

}
