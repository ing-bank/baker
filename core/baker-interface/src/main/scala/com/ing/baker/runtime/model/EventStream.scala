package com.ing.baker.runtime.model

import com.ing.baker.runtime.scaladsl.BakerEvent

trait EventStream[F[_]] {

  def publish(event: BakerEvent): F[Unit]
}
