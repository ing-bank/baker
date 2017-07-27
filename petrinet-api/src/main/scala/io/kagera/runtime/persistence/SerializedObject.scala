package io.kagera.runtime.persistence

case class SerializedObject(serializerId: Int, manifest: String, bytes: Array[Byte])
