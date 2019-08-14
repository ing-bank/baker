package com.ing.baker.runtime.actor.serialization

import akka.actor.ActorSystem
import akka.serialization._
import com.google.protobuf.ByteString
import com.ing.baker.runtime.actor.protobuf.SerializedData
import com.ing.baker.runtime.actor.serialization.modules._
import scalapb.GeneratedMessage

import scala.util.Try

import ProtoEventAdapterImpl._

object ProtoEventAdapterImpl {

  val defaultModules: Set[ProtoEventAdapterModule] = Set(
    new IntermediateLanguageModule,
    new ProcessIndexModule,
    new ProcessInstanceModule,
    new RecipeManagerModule,
    new RuntimeModule,
    new TypesModule
  )
}

class ProtoEventAdapterImpl(private val serialization: Serialization, encryption: Encryption, modules: Set[ProtoEventAdapterModule] = defaultModules) extends ProtoEventAdapter {

  def this(system: ActorSystem, encryption: Encryption) = this(SerializationExtension.get(system), encryption)

  // Combine all partial functions into one partial function
  val toProtoPF: PartialFunction[AnyRef, scalapb.GeneratedMessage] =
    modules
      .map(_.toProto(this))
      .reduce(_ orElse _)

  // Combine all partial functions into one partial function
  val toDomainPF: PartialFunction[scalapb.GeneratedMessage, AnyRef] =
    modules
      .map(_.toDomain(this))
      .reduce(_ orElse _)

  def toProto[T <: scalapb.GeneratedMessage](obj: AnyRef): T = toProtoMessage(obj).asInstanceOf[T]

  def toDomain[T](serializedMessage: scalapb.GeneratedMessage): T = toDomainObject(serializedMessage).asInstanceOf[T]

  def toProtoMessage(obj: AnyRef): scalapb.GeneratedMessage =
    toProtoPF.lift.apply(obj).getOrElse(
      throw new IllegalStateException(s"Cannot serialize object of type ${obj.getClass}"))

  def toDomainObject(serializedMessage: GeneratedMessage): AnyRef = serializedMessage match {

    case SerializedData(Some(serializerId), Some(manifest), Some(bytes)) ⇒

      val serializer = serialization.serializerByIdentity.getOrElse(serializerId,
        throw new IllegalStateException(s"No serializer found with id $serializerId")
      )

      val decryptedBytes = encryption.decrypt(bytes.toByteArray)

      serializer match {
        case s: SerializerWithStringManifest ⇒ s.fromBinary(decryptedBytes, manifest)
        case _                               ⇒
          val optionalClass = Try { Class.forName(manifest) }.toOption
          serializer.fromBinary(decryptedBytes, optionalClass)
      }

    case _ =>
      toDomainPF.lift.apply(serializedMessage).getOrElse(
        throw new IllegalStateException(s"Unknown protobuf message of type ${serializedMessage.getClass}"))
  }

  def getSerializerFor(obj: AnyRef): Serializer = serialization.findSerializerFor(obj)

  def toProtoAny(obj: AnyRef): SerializedData = {
    val serializer: Serializer = getSerializerFor(obj)
    val bytes = encryption.encrypt(serializer.toBinary(obj))

    val manifest = serializer match {
      case s: SerializerWithStringManifest ⇒ s.manifest(obj)
      case _                               ⇒ if (obj != null) obj.getClass.getName else ""
    }

    // we should not have to copy the bytes
    SerializedData(
      serializerId = Some(serializer.identifier),
      manifest = Some(manifest),
      data = Some(ByteString.copyFrom(bytes))
    )
  }
}
