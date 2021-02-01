package com.ing.bakery.common

import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri

import java.util.concurrent.atomic.AtomicInteger

/**
  * Failover only one request
  *
  * @param hosts host to failover
  */
sealed class FailoverState(
                            hosts: IndexedSeq[Uri],
                            legacyHosts: IndexedSeq[Uri] = IndexedSeq.empty) extends LazyLogging {
  private val allHosts = hosts ++ legacyHosts
  val size: Int = allHosts.size

  val currentPosition: AtomicInteger = new AtomicInteger(0)

  def failed(): Int = currentPosition.getAndUpdate((operand: Int) => if (operand + 1 < size) operand + 1 else 0)

  def uri: Uri = {
    val position = currentPosition.get()
    if (position >= hosts.size) {
      logger.warn("Failover to legacy baker!")
    }

    allHosts(position)
  }
}