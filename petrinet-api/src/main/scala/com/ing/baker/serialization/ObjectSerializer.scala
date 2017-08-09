package com.ing.baker.serialization

/**
 * Trait responsible for (de)serializing token values and transition output objects.
 */
trait ObjectSerializer {

  /**
    * Serializes an object to a SerializedObject instance
    *
    * @param obj
    * @return
    */
  def serializeObject(obj: AnyRef): SerializedObject

  /**
    * Deserializes an SerializedObject instance.
    *
    * @param data
    * @return
    */
  def deserializeObject(data: SerializedObject): AnyRef
}
