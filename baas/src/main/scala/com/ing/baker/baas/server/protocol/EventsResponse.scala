package com.ing.baker.baas.server.protocol

import cats.instances.list._
import cats.instances.try_._
import cats.syntax.traverse._
import com.ing.baker.runtime.akka.RuntimeEvent
import com.ing.baker.runtime.akka.actor.serialization.{ProtoMap, SerializersProvider}
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.baas.protobuf
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class EventsResponse(events: Seq[RuntimeEvent]) extends BaasResponse

object EventsResponse {

  implicit def protoMap(implicit provider: SerializersProvider): ProtoMap[EventsResponse, protobuf.EventsResponse] =
    new ProtoMap[EventsResponse, protobuf.EventsResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.EventsResponse] =
        protobuf.EventsResponse

      override def toProto(a: EventsResponse): protobuf.EventsResponse =
        protobuf.EventsResponse(a.events.map(ctxToProto(_)))

      override def fromProto(message: protobuf.EventsResponse): Try[EventsResponse] =
        for {
          events <- message.runtimeEvent.toList.traverse(ctxFromProto(_))
        } yield EventsResponse(events)
    }
}
