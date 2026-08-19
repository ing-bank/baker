package com.ing.baker.runtime.catseffect

import cats.effect.Sync

/**
  * Minimal synchronous effect capabilities used by model components.
  */
trait SyncSupport[F[_]] {
  def pure[A](value: A): F[A]
  def map[A, B](fa: F[A])(f: A => B): F[B]
  def flatMap[A, B](fa: F[A])(f: A => F[B]): F[B]
  def raiseError[A](throwable: Throwable): F[A]
  def delay[A](thunk: => A): F[A]
  def blocking[A](thunk: => A): F[A]
  def unit: F[Unit]
}

object SyncSupport {
  object syntax {
    implicit final class SyncEffectOps[F[_], A](private val fa: F[A]) {
      def map[B](f: A => B)(implicit sync: SyncSupport[F]): F[B] =
        sync.map(fa)(f)

      def flatMap[B](f: A => F[B])(implicit sync: SyncSupport[F]): F[B] =
        sync.flatMap(fa)(f)
    }
  }

  implicit def fromSync[F[_]](implicit sync: Sync[F]): SyncSupport[F] =
    new SyncSupport[F] {
      override def pure[A](value: A): F[A] = sync.pure(value)
      override def map[A, B](fa: F[A])(f: A => B): F[B] = sync.map(fa)(f)
      override def flatMap[A, B](fa: F[A])(f: A => F[B]): F[B] = sync.flatMap(fa)(f)
      override def raiseError[A](throwable: Throwable): F[A] = sync.raiseError(throwable)
      override def delay[A](thunk: => A): F[A] = sync.delay(thunk)
      override def blocking[A](thunk: => A): F[A] = sync.blocking(thunk)
      override def unit: F[Unit] = sync.unit
    }
}

