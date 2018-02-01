package com.ing.baker.runtime.actor

import com.google.protobuf.ByteString
import com.ing.baker.petrinet.api.PetriNet
import com.ing.baker.runtime.actor.messages._

package object serialization {

  implicit class SerializedObjectFns(obj: SerializedObject) {
    def toProto: SerializedData = SerializedData(Some(obj.serializerId), Some(obj.manifest), Some(ByteString.copyFrom(obj.bytes)))
  }

  implicit class SerializedDataFns(serialized: SerializedData) {
    def toDomain: SerializedObject =
      serialized match {
        case SerializedData(Some(serializerId), Some(manifest), Some(bytes)) ⇒ SerializedObject(serializerId, manifest, bytes.toByteArray)
        case _ => throw new IllegalStateException("Unable to deserialize, missing fields")
      }
    def deserialize(implicit objectSerializer: ObjectSerializer): AnyRef = objectSerializer.deserializeObject(serialized.toDomain)
  }
}