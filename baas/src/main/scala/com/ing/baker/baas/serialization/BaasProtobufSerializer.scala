package com.ing.baker.baas.serialization

import akka.actor.ExtendedActorSystem
import akka.serialization.{Serialization, SerializationExtension}
import com.ing.baker.baas.serialization.modules.BaasMessagesModule
import com.ing.baker.baas.server.protocol
import com.ing.baker.runtime.actor.serialization.BakerProtobufSerializer.Entry
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import com.ing.baker.runtime.actor.serialization.{BakerProtobufSerializer, ProtoEventAdapterImpl, ProtoEventAdapterModule}
import com.ing.baker.runtime.baas.protobuf
import com.ing.baker.baas.serialization.BaasProtobufSerializer._
import org.slf4j.LoggerFactory


object BaasProtobufSerializer {
  val baasModules: Set[ProtoEventAdapterModule] = Set(
    new BaasMessagesModule,
  )

  private val log = LoggerFactory.getLogger(classOf[BaasProtobufSerializer])

  // Hardcoded serializerId for this serializer. This should not conflict with other serializers.
  // Values from 0 to 40 are reserved for Akka internal usage.
  val identifier = 102

  val manifestInfo: Seq[Entry[_]]= Seq(
    BakerProtobufSerializer.Entry("com.ing.baker.baas.server.protocol.AddRecipeRequest", classOf[protocol.AddRecipeRequest], protobuf.AddRecipeRequest),
    BakerProtobufSerializer.Entry("com.ing.baker.baas.server.protocol.AddRecipeResponse", classOf[protocol.AddRecipeResponse], protobuf.AddRecipeResponse),
  )
}

class BaasProtobufSerializer(system: ExtendedActorSystem) extends BakerProtobufSerializer(system) {

  override def getSerializationExtension(): Serialization = SerializationExtension.get(system)

  // TODO remove this lazy modifier, but be aware removing lazy causes the tests to hang.
  override lazy val protoEventAdapter = new ProtoEventAdapterImpl(getSerializationExtension(), NoEncryption, ProtoEventAdapterImpl.defaultModules ++ BaasProtobufSerializer.baasModules)

  override def getManifestInfo(): Seq[Entry[_]] = super.getManifestInfo() ++ manifestInfo

  override def identifier: Int = BaasProtobufSerializer.identifier
}
