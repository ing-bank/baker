package com.ing.baker

import com.google.protobuf.ByteString
import com.ing.baker.serialization.common.SerializedData

package object serialization {

  implicit def transformSerializedObject(obj: SerializedObject): SerializedData = {
    SerializedData(Some(obj.serializerId), Some(obj.manifest), Some(ByteString.copyFrom(obj.bytes)))
  }

  implicit def transformSerializedData(serialized: SerializedData): SerializedObject = serialized match {
    case SerializedData(Some(serializerId), Some(manifest), Some(bytes)) ⇒
      SerializedObject(serializerId, manifest, bytes.toByteArray)
    case _ => throw new IllegalStateException("Unable to deserialize, missing fields")
  }
}
