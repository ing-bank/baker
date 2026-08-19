package com.ing.baker.runtime.common

import cats.effect.Sync
import cats.effect.kernel.Ref

/**
  * Minimal Ref allocation capability used by model components.
  */
trait RefState[F[_], A] {
  def get: F[A]
  def update(f: A => A): F[Unit]
  def modify[B](f: A => (A, B)): F[B]
}

trait RefSupport[F[_]] {
  def of[A](value: A): F[RefState[F, A]]
}

object RefSupport {

  private final case class CatsRefState[F[_], A](ref: Ref[F, A]) extends RefState[F, A] {
    override def get: F[A] = ref.get
    override def update(f: A => A): F[Unit] = ref.update(f)
    override def modify[B](f: A => (A, B)): F[B] = ref.modify(f)
  }

  implicit def fromSync[F[_]](implicit sync: Sync[F]): RefSupport[F] =
    new RefSupport[F] {
      override def of[A](value: A): F[RefState[F, A]] =
        sync.map(Ref.of[F, A](value))(CatsRefState(_))
    }
}

