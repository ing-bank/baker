package com.ing.baker.baas.protocol

import com.ing.baker.baas.protocol.ProtocolDistributedEventPublishing.Event
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.baker.runtime.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}

import scala.util.Try

object DistributedEventPublishingProto {

  implicit def eventProto: ProtoMap[Event, protobuf.Event] =
    new ProtoMap[Event, protobuf.Event] {

      val companion = protobuf.Event

      def toProto(a: Event): protobuf.Event =
        protobuf.Event(Some(ctxToProto(a.recipeEventMetadata)), Some(ctxToProto(a.event)))

      def fromProto(message: protobuf.Event): Try[Event] =
        for {
          recipeEventMetadataProto <- versioned(message.recipeEventMetadata, "recipeEventMetadata")
          recipeEventMetadata <- ctxFromProto(recipeEventMetadataProto)
          eventProto <- versioned(message.event, "event")
          event <- ctxFromProto(eventProto)
        } yield Event(recipeEventMetadata, event)
    }

}
