package com.ing.baker.runtime.actortyped.serialization.protomappings

import com.ing.baker.il
import com.ing.baker.il.EventOutputTransformer
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping.versioned

import scala.util.Try

class EventOutputTransformerMapping extends ProtobufMapping[il.EventOutputTransformer] {

  override type ProtoClass = protobuf.EventOutputTransformer

  override def toProto(transformer: EventOutputTransformer): protobuf.EventOutputTransformer =
    protobuf.EventOutputTransformer(Option(transformer.newEventName), transformer.ingredientRenames)

  override def fromProto(message: protobuf.EventOutputTransformer): Try[EventOutputTransformer] =
    versioned(message.newEventName, "newEventName").map(name => il.EventOutputTransformer(name, message.ingredientRenames))

}
