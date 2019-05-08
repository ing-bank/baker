package com.ing.baker.runtime.core.actor.process_index

import com.ing.baker.runtime.core.actor.process_index.ProcessEventReceiver.ProcessEventRejected
import com.ing.baker.runtime.core.actor.serialization.ProtoMap
import com.ing.baker.runtime.core.actor.serialization.ProtoMap.versioned
import scalapb.GeneratedMessageCompanion

import scala.util.Try

object ProcessEventReceiverProto {

  implicit def processEventRejected: ProtoMap[ProcessEventRejected, protobuf.ProcessEventRejected] =
    new ProtoMap[ProcessEventRejected, protobuf.ProcessEventRejected] {

      override def companion: GeneratedMessageCompanion[protobuf.ProcessEventRejected] =
        protobuf.ProcessEventRejected

      override def toProto(a: ProcessEventRejected): protobuf.ProcessEventRejected =
        protobuf.ProcessEventRejected(Some(a.message))

      override def fromProto(message: protobuf.ProcessEventRejected): Try[ProcessEventRejected] =
        for {
          message <- versioned(message.message, "queue")
        } yield ProcessEventRejected(message)
    }

}
