package com.ing.baker.runtime.serialization

import akka.actor.ExtendedActorSystem
import akka.serialization.SerializerWithStringManifest
import com.ing.baker.runtime.serialization.TypedProtobufSerializer.BinarySerializable
import org.slf4j.LoggerFactory

import scala.reflect.ClassTag
import scala.util.Try

object TypedProtobufSerializer {

  private val log = LoggerFactory.getLogger(classOf[TypedProtobufSerializer])

  /** Hardcoded serializerId for this serializer. This should not conflict with other serializers.
    * Values from 0 to 40 are reserved for Akka internal usage.
    */
  val identifier = 101

  def forType[A <: AnyRef](implicit tag: ClassTag[A]): RegisterFor[A] = new RegisterFor[A](tag)

  class RegisterFor[A <: AnyRef](classTag: ClassTag[A]) {

    def register[P <: scalapb.GeneratedMessage with scalapb.Message[P]](implicit protoMap: ProtoMap[A, P]): BinarySerializable =
      register[P](None)

    def register[P <: scalapb.GeneratedMessage with scalapb.Message[P]](overrideName: String)(implicit protoMap: ProtoMap[A, P]): BinarySerializable =
      register[P](Some(overrideName))

    def register[P <: scalapb.GeneratedMessage with scalapb.Message[P]](overrideName: Option[String])(implicit protoMap: ProtoMap[A, P]): BinarySerializable = {
      new BinarySerializable {

        override type Type = A

        override val tag: Class[_] = classTag.runtimeClass

        override val manifest: String = overrideName.getOrElse(classTag.runtimeClass.getName)

        override def toBinary(a: Type): Array[Byte] = protoMap.toByteArray(a)

        override def fromBinary(binary: Array[Byte]): Try[Type] = protoMap.fromByteArray(binary)
      }
    }
  }

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
}

abstract class TypedProtobufSerializer(system: ExtendedActorSystem, entries: SerializersProvider => List[BinarySerializable]) extends SerializerWithStringManifest {

  def serializersProvider: SerializersProvider =
    SerializersProvider(system, system.provider)

  lazy val entriesMem: List[BinarySerializable] =
    entries(serializersProvider)

  override def identifier: Int =
    TypedProtobufSerializer.identifier

  override def manifest(o: AnyRef): String = {
    entriesMem
      .find(_.isInstance(o))
      .map(_.manifest)
      .getOrElse(throw new IllegalStateException(s"Unsupported object of type: ${o.getClass}"))
  }

  override def toBinary(o: AnyRef): Array[Byte] =
    entriesMem
      .find(_.isInstance(o))
      .map(_.unsafeToBinary(o))
      .getOrElse(throw new IllegalStateException(s"Unsupported object of type: ${o.getClass}"))

  override def fromBinary(bytes: Array[Byte], manifest: String): AnyRef =
    entriesMem
      .find(_.manifest == manifest)
      .map(_.fromBinaryAnyRef(bytes))
      .getOrElse(throw new IllegalStateException(s"Unsupported object with manifest $manifest"))
      .fold(
        { e => TypedProtobufSerializer.log.error(s"Failed to deserialize bytes with manifest $manifest", e); throw e },
        identity
      )
}

