package com.ing.baker.runtime.actor.processindex

import com.google.common.collect.Sets

import scala.collection.convert.decorateAsScala._


class LocalProcessInstanceStore extends ProcessInstanceStore {
  private val allProcessesMetadata = Sets.newConcurrentHashSet[ProcessMetadata]()

  override def getAll: Set[ProcessMetadata] = allProcessesMetadata.asScala.toSet

  override def add(meta: ProcessMetadata): Unit = {
    allProcessesMetadata.add(meta)
  }

  override def remove(meta: ProcessMetadata): Unit = {
    allProcessesMetadata.remove(meta)
  }
}
