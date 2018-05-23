package com.ing.baker.runtime.actor.serialization

import java.io.ByteArrayOutputStream

import akka.actor.ExtendedActorSystem
import akka.serialization.SerializerWithStringManifest
import scalapb.{GeneratedMessageCompanion, Message}
import com.typesafe.config.Config

import scala.collection.JavaConverters._

object ScalaPBSerializer {
  import scala.reflect.runtime.{universe => ru}

  private lazy val universeMirror = ru.runtimeMirror(getClass.getClassLoader)

  def scalaPBTypes(clazz: Class[_ <: AnyRef]): (Class[_ <: AnyRef], GeneratedMessageCompanion[_]) = {
    val classSymbol = universeMirror.classSymbol(clazz)
    val moduleMirror = universeMirror.reflectModule(classSymbol.companion.asModule)
    clazz -> moduleMirror.instance.asInstanceOf[GeneratedMessageCompanion[_] with Message[_]]
  }

  def getManifests(config: Config): Map[String, (Class[_ <: AnyRef], GeneratedMessageCompanion[_])] = {
    config.entrySet().asScala.map { entry =>

      val manifest = entry.getKey
      val className = entry.getValue.unwrapped().asInstanceOf[String]
      val clazz = Class.forName(className).asInstanceOf[Class[AnyRef]]

      manifest -> scalaPBTypes(clazz)
    }.toMap
  }
}

class ScalaPBSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest {

  import ScalaPBSerializer._

  private val manifests: Map[String, (Class[_ <: AnyRef], GeneratedMessageCompanion[_])] =
    getManifests(system.settings.config.getConfig("baker.scalapb.serialization-manifests"))

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
      case msg: scalapb.GeneratedMessage =>
        val stream: ByteArrayOutputStream = new ByteArrayOutputStream()
        msg.writeTo(stream)
        stream.toByteArray
    }
  }
}