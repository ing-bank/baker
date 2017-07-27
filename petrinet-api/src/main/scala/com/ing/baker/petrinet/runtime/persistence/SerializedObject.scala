package com.ing.baker.petrinet.runtime.persistence

case class SerializedObject(serializerId: Int, manifest: String, bytes: Array[Byte])
