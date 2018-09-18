package com.ing.baker.runtime.actor.serialization

import akka.actor.ExtendedActorSystem
import akka.serialization.SerializerWithStringManifest
import com.ing.baker.il
import com.ing.baker.runtime.actor.process_index.{ProcessIndex, ProcessIndexProtocol}
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actor.recipe_manager.{RecipeManager, RecipeManagerProtocol}
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import com.ing.baker.runtime.{actor, core}
import scalapb.{GeneratedMessage, GeneratedMessageCompanion, Message}
import org.slf4j.LoggerFactory

object BakerProtobufSerializer {
  case class Entry[A <: GeneratedMessage with Message[A]](manifest: String, domainClass: Class[_], pbt: GeneratedMessageCompanion[A])

  private val log = LoggerFactory.getLogger(classOf[BakerProtobufSerializer])
}

class BakerProtobufSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest {
  import BakerProtobufSerializer._

  // TODO remove this lazy modifier, but be aware removing lazy causes the tests to hang.
  private lazy val protoEventAdapter = new ProtoEventAdapter(new ObjectSerializer(system, NoEncryption))

  val manifestInfo = Seq(
    Entry("core.RuntimeEvent", classOf[core.RuntimeEvent], protobuf.RuntimeEvent),
    Entry("core.ProcessState", classOf[core.ProcessState], protobuf.ProcessState),

    Entry("il.CompiledRecipe", classOf[il.CompiledRecipe], protobuf.CompiledRecipe),

    Entry("ProcessIndex.ActorCreated", classOf[ProcessIndex.ActorCreated], actor.process_index.protobuf.ActorCreated),
    Entry("ProcessIndex.ActorPassivated", classOf[ProcessIndex.ActorPassivated], actor.process_index.protobuf.ActorPassivated),
    Entry("ProcessIndex.ActorActivated", classOf[ProcessIndex.ActorActivated], actor.process_index.protobuf.ActorActivated),
    Entry("ProcessIndex.ActorDeleted", classOf[ProcessIndex.ActorDeleted], actor.process_index.protobuf.ActorDeleted),
    Entry("ProcessIndex.ActorMetadata", classOf[ProcessIndex.ActorMetadata], actor.process_index.protobuf.ActorMetaData),
    Entry("ProcessIndexProtocol.GetIndex", ProcessIndexProtocol.GetIndex.getClass, actor.process_index.protobuf.GetIndex),
    Entry("ProcessIndexProtocol.Index", classOf[ProcessIndexProtocol.Index], actor.process_index.protobuf.Index),
    Entry("ProcessIndexProtocol.CreateProcess", classOf[ProcessIndexProtocol.CreateProcess], actor.process_index.protobuf.CreateProcess),
    Entry("ProcessIndexProtocol.ProcessEvent", classOf[ProcessIndexProtocol.ProcessEvent], actor.process_index.protobuf.ProcessEvent),

    Entry("RecipeManager.RecipeAdded", classOf[RecipeManager.RecipeAdded], actor.recipe_manager.protobuf.RecipeAdded),
    Entry("RecipeManagerProtocol.AddRecipe", classOf[RecipeManagerProtocol.AddRecipe], actor.recipe_manager.protobuf.AddRecipe),
    Entry("RecipeManagerProtocol.AddRecipeResponse", classOf[RecipeManagerProtocol.AddRecipeResponse], actor.recipe_manager.protobuf.AddRecipeResponse),
    Entry("RecipeManagerProtocol.GetRecipe", classOf[RecipeManagerProtocol.GetRecipe], actor.recipe_manager.protobuf.GetRecipe),
    Entry("RecipeManagerProtocol.RecipeFound", classOf[RecipeManagerProtocol.RecipeFound], actor.recipe_manager.protobuf.RecipeFound),
    Entry("RecipeManagerProtocol.NoRecipeFound", classOf[RecipeManagerProtocol.NoRecipeFound], actor.recipe_manager.protobuf.NoRecipeFound),
    Entry("RecipeManagerProtocol.GetAllRecipes", RecipeManagerProtocol.GetAllRecipes.getClass, actor.recipe_manager.protobuf.GetAllRecipes),
    Entry("RecipeManagerProtocol.AllRecipes", classOf[RecipeManagerProtocol.AllRecipes], actor.recipe_manager.protobuf.AllRecipes)
  )

  // Hardcoded serializerId for this serializer. This should not conflict with other serializers.
  // Values from 0 to 40 are reserved for Akka internal usage.
  override def identifier: Int = 101

  override def manifest(o: AnyRef): String = {

    manifestInfo
      .find(_.domainClass.isInstance(o))
      .map(_.manifest)
      .getOrElse(throw new IllegalStateException(s"Unsupported object of type: ${o.getClass}"))
  }

  override def toBinary(o: AnyRef): Array[Byte] = {
    try {
      protoEventAdapter.toProto(o).toByteArray
    } catch {
      case e: Throwable =>
        log.error(s"Failed to serialize object $o", e)
        throw e;
    }
  }

  override def fromBinary(bytes: Array[Byte], manifest: String): AnyRef = {
    try {
      val pbt = manifestInfo
        .find(_.manifest == manifest)
        .map(_.pbt)
        .getOrElse(throw new IllegalStateException(s"Unknown manifest: $manifest"))

      val protobuf = pbt.parseFrom(bytes).asInstanceOf[GeneratedMessage]

      protoEventAdapter.toDomain(protobuf)
    } catch {
      case e: Throwable =>
        log.error(s"Failed to deserialize bytes with manifest $manifest", e)
        throw e;
    }
  }
}
