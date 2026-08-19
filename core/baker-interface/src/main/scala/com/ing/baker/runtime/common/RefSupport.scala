package com.ing.baker.runtime.common

import cats.effect.Sync
import cats.effect.kernel.Ref

/**
  * Minimal Ref allocation capability used by model components.
  */
trait RefSupport[F[_]] {
  def of[A](value: A): F[Ref[F, A]]
}

object RefSupport {

  implicit def fromSync[F[_]](implicit sync: Sync[F]): RefSupport[F] =
    new RefSupport[F] {
      override def of[A](value: A): F[Ref[F, A]] =
        Ref.of[F, A](value)
    }
}

