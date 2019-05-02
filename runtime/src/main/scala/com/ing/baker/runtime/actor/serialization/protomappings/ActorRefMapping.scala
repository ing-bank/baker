package com.ing.baker.runtime.actor.serialization.protomappings

import akka.actor.ActorRef
import com.ing.baker.runtime.actor.serialization.{ProtoMap, SerializersProvider}
import com.ing.baker.runtime.actor.serialization.ProtoMap.versioned
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actor.protobuf.ActorRefId

import scala.util.Try

class ActorRefMapping(provider: SerializersProvider) extends ProtoMap[ActorRef, protobuf.ActorRefId] {

  val companion = protobuf.ActorRefId

  override def toProto(a: ActorRef): ActorRefId =
    protobuf.ActorRefId(Some(akka.serialization.Serialization.serializedActorPath(a)))

  override def fromProto(message: ActorRefId): Try[ActorRef] =
    for {
      identifier <- versioned(message.identifier, "identifier")
      actorRef <- Try(provider.actorRefProvider.resolveActorRef(identifier))
    } yield actorRef
}
