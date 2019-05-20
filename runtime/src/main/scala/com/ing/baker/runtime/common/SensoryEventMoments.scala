package com.ing.baker.runtime.common

trait SensoryEventMoments[F[_], Seq[_], Map[_, _], R <: SensoryEventResult[Seq, Map]] {

  def received: F[SensoryEventStatus]

  def completed: F[R]
}


