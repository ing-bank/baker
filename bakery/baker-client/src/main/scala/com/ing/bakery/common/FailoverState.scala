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
  val size: Int = hosts.size
  val allSize: Int = allHosts.size

  val currentPosition: AtomicInteger = new AtomicInteger(0)

  def failed(): Int = currentPosition.getAndUpdate((operand: Int) => if (operand + 1 < size) operand + 1 else 0)

  def failoverToLegacy(): Unit = {

    if (legacyHosts.isEmpty) {
      logger.warn("Legacy hosts are not defined")
      failed()
    } else {
      currentPosition.getAndUpdate {
        operand: Int =>
          if (operand + 1 < allSize && operand >= size) operand + 1
          else size
      }
    }
  }

  def uri: Uri = {
    allHosts(currentPosition.get())
  }
}