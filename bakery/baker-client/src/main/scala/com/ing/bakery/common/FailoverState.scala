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
sealed class FailoverState(var endpoint: EndpointConfig) extends LazyLogging {

  private var size: Int = endpoint.hosts.size
  private val currentPosition: AtomicInteger = new AtomicInteger(0)

  def failed(): Unit =
    currentPosition.getAndUpdate((operand: Int) => if (operand + 1 < size) operand + 1 else 0)

  def fallback(alternative: EndpointConfig): Unit = {
    endpoint = alternative
    size = endpoint.hosts.size
    currentPosition.set(0)
  }

  def uri: Uri = endpoint.hosts(currentPosition.get())
}