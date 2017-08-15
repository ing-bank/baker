package com.ing.baker

import com.google.protobuf.ByteString

package object serialization {

  implicit def transformToProto(obj: SerializedObject): common.SerializedData = {
    common.SerializedData(Some(obj.serializerId), Some(obj.manifest), Some(ByteString.copyFrom(obj.bytes)))
  }

  implicit def transformFromProto(serialized: common.SerializedData): SerializedObject = serialized match {
    case common.SerializedData(Some(serializerId), Some(manifest), Some(bytes)) ⇒ SerializedObject(serializerId, manifest, bytes.toByteArray)
    case _ => throw new IllegalStateException("Unable to deserialize, missing fields")
  }
}