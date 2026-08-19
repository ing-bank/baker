package com.ing.baker.runtime.catseffect

import cats.effect.Async
import fs2.Stream

/**
  * Minimal fs2 compilation capabilities used by model components.
  */
trait Fs2Support[F[_]] {
  def drain[A](stream: Stream[F, A]): F[Unit]
  def lastOrError[A](stream: Stream[F, A]): F[A]
}

object Fs2Support {

  implicit def fromAsync[F[_]](implicit async: Async[F]): Fs2Support[F] =
    new Fs2Support[F] {
      override def drain[A](stream: Stream[F, A]): F[Unit] =
        stream.compile.drain

      override def lastOrError[A](stream: Stream[F, A]): F[A] =
        stream.compile.lastOrError
    }
}

