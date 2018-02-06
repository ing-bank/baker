package com.ing.baker.runtime.actor.serialization

import akka.actor.ExtendedActorSystem
import akka.serialization.SerializerWithStringManifest
import com.ing.baker.il
import com.ing.baker.runtime.actor.process_index.ProcessIndex
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager
import com.ing.baker.runtime.{actor, core}
import com.trueaccord.scalapb.{GeneratedMessage, GeneratedMessageCompanion, Message}

case class Entry[A <: GeneratedMessage with Message[A]](manifest: String, domainClass: Class[_], pbt: GeneratedMessageCompanion[A])

class BakerProtobufSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest with ProtoEventAdapter {

  lazy val objectSerializer = new ObjectSerializer(system)

  val manifestInfo = Seq(
    Entry("core.RuntimeEvent", classOf[core.RuntimeEvent], protobuf.RuntimeEvent),
    Entry("core.ProcessState", classOf[core.ProcessState], protobuf.ProcessState),
    Entry("il.CompiledRecipe", classOf[il.CompiledRecipe], protobuf.CompiledRecipe),

    Entry("ProcessIndex.ActorCreated", classOf[ProcessIndex.ActorCreated], actor.process_index.protobuf.ActorCreated),
    Entry("ProcessIndex.ActorPassivated", classOf[ProcessIndex.ActorPassivated], actor.process_index.protobuf.ActorPassivated),
    Entry("ProcessIndex.ActorActivated", classOf[ProcessIndex.ActorActivated], actor.process_index.protobuf.ActorActivated),
    Entry("ProcessIndex.ActorDeleted", classOf[ProcessIndex.ActorDeleted], actor.process_index.protobuf.ActorDeleted),

    Entry("RecipeManager.RecipeAdded", classOf[RecipeManager.RecipeAdded], actor.recipe_manager.protobuf.RecipeAdded)
  )

  // Hardcoded serializerId for this serializer. This should not conflict with other serializers.
  // Values from 0 to 40 are reserved for Akka internal usage.
  override def identifier: Int = 101

  override def manifest(o: AnyRef): String = {

    manifestInfo
      .find(_.domainClass.isInstance(o))
      .map(_.manifest)
      .getOrElse(throw new IllegalStateException(s"Unsupported object: $o"))
  }

  override def toBinary(o: AnyRef): Array[Byte] = toProto(o).toByteArray

  override def fromBinary(bytes: Array[Byte], manifest: String): AnyRef = {

    val pbt = manifestInfo
      .find(_.manifest == manifest)
      .map(_.pbt)
      .getOrElse(throw new IllegalStateException(s"Unkown manifest: $manifest"))

    val protobuf = pbt.parseFrom(bytes).asInstanceOf[GeneratedMessage]

    toDomain(protobuf)
  }
}
