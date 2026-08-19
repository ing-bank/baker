package com.ing.baker.runtime.common

trait FunctionK[F[_], G[_]] {
  def apply[A](fa: F[A]): G[A]
}

object FunctionK {
  def id[F[_]]: FunctionK[F, F] = new FunctionK[F, F] {
    override def apply[A](fa: F[A]): F[A] = fa
  }
}
