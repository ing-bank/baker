package io.kagera.akka.actor

import java.io.ByteArrayOutputStream
import java.nio.ByteBuffer
import java.nio.charset.Charset

import akka.actor.ExtendedActorSystem
import akka.serialization.SerializerWithStringManifest
import com.trueaccord.scalapb.{GeneratedMessage, GeneratedMessageCompanion, Message}
import io.kagera.akka.actor.ScalaPBSerializer._
import io.kagera.runtime.persistence.messages._

object ScalaPBSerializer {
  import scala.reflect.runtime.{universe => ru}

  private lazy val universeMirror = ru.runtimeMirror(getClass.getClassLoader)

  def scalaPBType[T <: GeneratedMessage with Message[T]](implicit tt: ru.TypeTag[T]) = {
    val messageType = universeMirror.runtimeClass(ru.typeOf[T].typeSymbol.asClass).asInstanceOf[Class[T]]
    val companionType = universeMirror.reflectModule(ru.typeOf[T].typeSymbol.companion.asModule).instance.asInstanceOf[GeneratedMessageCompanion[T]]
    messageType -> companionType
  }

  val UTF8: Charset = Charset.forName("UTF-8")
  val Identifier: Int = ByteBuffer.wrap("akka-scalapb-serializer".getBytes(UTF8)).getInt
}

class ScalaPBSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest {

  def manifests: Map[String, (Class[_ <: AnyRef], GeneratedMessageCompanion[_ <: GeneratedMessage])] = Map(
    "TransitionFired" -> scalaPBType[TransitionFired],
    "TransitionFailed" -> scalaPBType[TransitionFailed],
    "Initialized" -> scalaPBType[Initialized]
  )

  private val class2ManifestMap: Map[Class[_ <: AnyRef], String] = manifests.map {
    case (key, value) => value._1 -> key
  }.toMap

  override def identifier: Int = ScalaPBSerializer.Identifier

  override def fromBinary(bytes: Array[Byte], manifest: String): AnyRef = {
    manifests.get(manifest).
      map { case (_, companion) => companion.parseFrom(bytes) }.
      getOrElse(throw new IllegalArgumentException(s"Cannot deserialize byte array with manifest $manifest"))
  }

  override def manifest(o: AnyRef): String = {
    class2ManifestMap(o.getClass)
  }

  override def toBinary(o: AnyRef): Array[Byte] = {
    o match {
      case msg: com.trueaccord.scalapb.GeneratedMessage =>
        val stream: ByteArrayOutputStream = new ByteArrayOutputStream()
        msg.writeTo(stream)
        stream.toByteArray
    }
  }
}