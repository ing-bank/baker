package com.ing.baker.runtime.actor.process_instance.internal

/**
 * Describes the exception state of a transition.
 *
 * @param failureTime The time of the last failure.
 * @param failureCount The number of times the transition failed in sequence.
 * @param failureReason The reason message of the last failure.
 * @param failureStrategy The chosen strategy to deal with the last failure.
 */
case class ExceptionState(
  failureTime: Long,
  failureCount: Int,
  failureReason: String,
  failureStrategy: ExceptionStrategy)