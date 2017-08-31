package com.ing.baker.runtime.actor

import com.google.protobuf.ByteString
import com.ing.baker.runtime.actor.messages._

package object serialization {

  implicit def transformToProto(obj: SerializedObject): SerializedData = {
    SerializedData(Some(obj.serializerId), Some(obj.manifest), Some(ByteString.copyFrom(obj.bytes)))
  }

  implicit def transformFromProto(serialized: SerializedData): SerializedObject = serialized match {
    case SerializedData(Some(serializerId), Some(manifest), Some(bytes)) ⇒ SerializedObject(serializerId, manifest, bytes.toByteArray)
    case _ => throw new IllegalStateException("Unable to deserialize, missing fields")
  }
}