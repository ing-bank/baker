package com.ing.baker.runtime.actor.process_index

trait ProcessInstanceStore {

  def getAll: Set[ProcessMetadata]

  def add(meta: ProcessMetadata): Unit

  def remove(meta: ProcessMetadata): Unit
}
