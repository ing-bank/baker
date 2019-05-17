package com.ing.baker.runtime.common

trait SensoryEventMoments[F[_], R <: SensoryEventResult[_, _]] {

  def received: F[SensoryEventStatus]

  def completed: F[R]
}


