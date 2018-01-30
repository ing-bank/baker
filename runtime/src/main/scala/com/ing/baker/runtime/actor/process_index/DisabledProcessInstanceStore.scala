package com.ing.baker.runtime.actor.process_index


class DisabledProcessInstanceStore extends ProcessInstanceStore {
  override val getAll: Set[ProcessMetadata] = Set.empty

  override def add(meta: ProcessMetadata): Unit = {
    // Intentionally left blank
  }

  override def remove(meta: ProcessMetadata): Unit = {
    // Intentionally left blank
  }
}
