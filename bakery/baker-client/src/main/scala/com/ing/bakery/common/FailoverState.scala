package com.ing.bakery.common

import com.ing.bakery.scaladsl.EndpointConfig
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri

import java.util.concurrent.atomic.AtomicInteger

/**
  * Failover only one request
  *
  * @param hosts host to failover
  */
sealed class FailoverState(val endpoint: EndpointConfig) extends LazyLogging {
  val size: Int = endpoint.hosts.size
  val currentPosition: AtomicInteger = new AtomicInteger(0)

  def failed(): Unit =
    currentPosition.getAndUpdate((operand: Int) => if (operand + 1 < size) operand + 1 else 0)

  def uri: Uri = endpoint.hosts(currentPosition.get())
}