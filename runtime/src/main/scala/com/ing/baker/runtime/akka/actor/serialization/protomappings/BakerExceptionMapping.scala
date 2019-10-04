package com.ing.baker.runtime.akka.actor.serialization.protomappings

import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.versioned
import com.ing.baker.runtime.common.BakerException

import scala.util.Try

class BakerExceptionMapping extends ProtoMap[BakerException, protobuf.BakerException] {

    val companion: protobuf.BakerException.type = protobuf.BakerException

    override def toProto(a: BakerException): protobuf.BakerException =
      BakerException.encode(a) match {
        case (message, enum) =>
          protobuf.BakerException(Some(message), Some(enum))
      }

    override def fromProto(message: protobuf.BakerException): Try[BakerException] =
      for {
        msg <- versioned(message.message, "message")
        enum <- versioned(message.enum, "enum")
        decoded <- BakerException.decode(msg, enum)
      } yield decoded
  }
