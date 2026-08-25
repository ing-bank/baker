package com.ing.baker.runtime.catseffect

import cats.Applicative

import java.util.concurrent.{CompletableFuture, CompletionStage}

/**
  * Minimal effect capabilities required to construct interaction instances from reflection.
  */
trait EffectSupport[F[_]] {
  def pure[A](value: A): F[A]
  def map[A, B](fa: F[A])(f: A => B): F[B]
}

object EffectSupport {
  type CompletionStageF[A] = CompletionStage[A]
  type CompletableFutureF[A] = CompletableFuture[A]

  def fromSyncSupport[F[_]](implicit sync: SyncSupport[F]): EffectSupport[F] =
    new EffectSupport[F] {
      override def pure[A](value: A): F[A] = sync.pure(value)
      override def map[A, B](fa: F[A])(f: A => B): F[B] = sync.map(fa)(f)
    }

  implicit def fromApplicative[F[_]](implicit applicative: Applicative[F]): EffectSupport[F] =
    new EffectSupport[F] {
      override def pure[A](value: A): F[A] = applicative.pure(value)
      override def map[A, B](fa: F[A])(f: A => B): F[B] = applicative.map(fa)(f)
    }

  val fromCompletionStage: EffectSupport[CompletionStageF] =
    fromSyncSupport(SyncSupport.fromCompletionStage)

  val fromCompletableFuture: EffectSupport[CompletableFutureF] =
    fromSyncSupport(SyncSupport.fromCompletableFuture)
}

