package com.ing.baker.runtime.serialization.protomappings

import com.ing.baker.il
import com.ing.baker.il.EventOutputTransformer
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.serialization.ProtoMap.versioned
import com.ing.baker.runtime.serialization.ProtoMap

import scala.util.Try

class EventOutputTransformerMapping extends ProtoMap[il.EventOutputTransformer, protobuf.EventOutputTransformer] {

  val companion = protobuf.EventOutputTransformer

  override def toProto(transformer: EventOutputTransformer): protobuf.EventOutputTransformer =
    protobuf.EventOutputTransformer(Option(transformer.newEventName), transformer.ingredientRenames)

  override def fromProto(message: protobuf.EventOutputTransformer): Try[EventOutputTransformer] =
    versioned(message.newEventName, "newEventName").map(name => il.EventOutputTransformer(name, message.ingredientRenames))

}
