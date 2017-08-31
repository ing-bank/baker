package com.ing.baker.runtime.actor.serialization

import java.io.ByteArrayOutputStream

import akka.actor.ExtendedActorSystem
import akka.serialization.SerializerWithStringManifest
import com.trueaccord.scalapb.{GeneratedMessageCompanion, Message}
import com.typesafe.config.Config

import scala.collection.JavaConversions.asScalaSet

object ScalaPBSerializer {
  import scala.reflect.runtime.{universe => ru}

  private lazy val universeMirror = ru.runtimeMirror(getClass.getClassLoader)

  def scalaPBType(clazz: Class[_ <: AnyRef]): (Class[_ <: AnyRef], GeneratedMessageCompanion[_]) = {
    val classSymbol = universeMirror.classSymbol(clazz)
    val moduleMirror = universeMirror.reflectModule(classSymbol.companion.asModule)
    clazz -> moduleMirror.instance.asInstanceOf[GeneratedMessageCompanion[_] with Message[_]]
  }
}

class ScalaPBSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest {

  import ScalaPBSerializer._

  private val manifests: Map[String, (Class[_ <: AnyRef], GeneratedMessageCompanion[_])] = {
    val config: Config = system.settings.config.getConfig("baker.scalapb.serialization-manifests")
    config.entrySet().map { entry =>
      val manifest = entry.getKey
      val clazz = Class.forName(entry.getValue.unwrapped().asInstanceOf[String]).asInstanceOf[Class[AnyRef]]
      manifest -> scalaPBType(clazz)
    }.toMap
  }

  //noinspection RedundantCollectionConversion
  private val class2ManifestMap: Map[Class[_ <: AnyRef], String] = manifests.map {
    case (manifest, (clazz, _)) => clazz -> manifest
  }.toMap

  // Hardcoded serializerId for this serializer. This should not conflict with other serializers.
  // Values from 0 to 40 are reserved for Akka internal usage.
  override def identifier: Int = 102

  override def fromBinary(bytes: Array[Byte], manifest: String): AnyRef = {
    manifests.get(manifest).
      map { case (_, companion) => companion.parseFrom(bytes).asInstanceOf[AnyRef] }.
      getOrElse(throw new IllegalArgumentException(s"Cannot deserialize byte array with manifest $manifest"))
  }

  override def manifest(o: AnyRef): String = {
    class2ManifestMap.getOrElse(o.getClass, throw new IllegalStateException(s"Manifest config not found for class ${o.getClass}"))
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