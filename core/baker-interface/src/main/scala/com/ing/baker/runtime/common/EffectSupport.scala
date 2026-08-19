package com.ing.baker.runtime.common

import cats.Applicative

/**
  * Minimal effect capabilities required to construct interaction instances from reflection.
  */
trait EffectSupport[F[_]] {
  def pure[A](value: A): F[A]
  def map[A, B](fa: F[A])(f: A => B): F[B]
}

object EffectSupport {
  implicit def fromApplicative[F[_]](implicit applicative: Applicative[F]): EffectSupport[F] =
    new EffectSupport[F] {
      override def pure[A](value: A): F[A] = applicative.pure(value)
      override def map[A, B](fa: F[A])(f: A => B): F[B] = applicative.map(fa)(f)
    }
}

