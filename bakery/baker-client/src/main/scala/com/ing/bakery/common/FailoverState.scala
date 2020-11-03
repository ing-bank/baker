package com.ing.bakery.common

import java.util.concurrent.atomic.AtomicInteger

import org.http4s.Uri

/**
  * Failover only one request
  * @param hosts host to failover
  */
sealed class FailoverState(hosts: IndexedSeq[Uri]) {
  val size = hosts.size

  val currentPosition: AtomicInteger = new AtomicInteger(0)

  def failed(): Int = currentPosition.getAndUpdate((operand: Int) => if (operand + 1 < size) operand + 1 else 0)

  def uri: Uri = hosts(currentPosition.get())
}