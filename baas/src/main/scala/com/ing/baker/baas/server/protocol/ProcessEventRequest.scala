package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.core.RuntimeEvent

import com.ing.baker.runtime.actor.serialization.ProtoMap
import com.ing.baker.runtime.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.baas.protobuf
import scalapb.GeneratedMessageCompanion

import scala.util.Try

case class ProcessEventRequest(event: RuntimeEvent) extends BaasRequest

object ProcessEventRequest {

  implicit def protoMap: ProtoMap[ProcessEventRequest, protobuf.ProcessEventRequest] =
    new ProtoMap[ProcessEventRequest, protobuf.ProcessEventRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.ProcessEventRequest] =
        protobuf.ProcessEventRequest

      override def toProto(a: ProcessEventRequest): protobuf.ProcessEventRequest =
        protobuf.ProcessEventRequest(Some(ctxToProto(a.event)))

      override def fromProto(message: protobuf.ProcessEventRequest): Try[ProcessEventRequest] =
        for {
          eventProto <- versioned(message.runtimeEvent, "runtimeEvent")
          event <- ctxFromProto(eventProto)
        } yield ProcessEventRequest(event)
    }
}
