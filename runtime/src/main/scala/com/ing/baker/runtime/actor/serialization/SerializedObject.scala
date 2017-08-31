package com.ing.baker.runtime.actor.serialization

/**
  * This object wraps a byte array with some meta data.
  *
  * @param serializerId The identifier of the serializer used to create this object.
  * @param manifest A manifest indicating the 'type' of object that is serialized.
  * @param bytes The serialized object data.
  */
case class SerializedObject(serializerId: Int, manifest: String, bytes: Array[Byte])
