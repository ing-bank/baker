package io.kagera.runtime.persistence

/**
 * Trait responsible for (de)serializing token values and transition output objects.
 */
trait ObjectSerializer {

  def serializeObject(obj: AnyRef): SerializedObject

  def deserializeObject(data: SerializedObject): AnyRef
}
