package com.ing.baker.runtime.model

import cats.kernel.Monoid
import cats.syntax.either._

case class AsyncModel[S, +E, +A](action: (Int, S) => (Int, S, Either[List[E], A])) {

  def run(implicit noState: Unit =:= S): (Int, S, Either[List[E], A]) =
    action(0, noState(()))

  def run(state0: S): (Int, S, Either[List[E], A]) =
    action(0, state0)

  def map[B](f: A => B): AsyncModel[S, E, B] =
    AsyncModel { (time0, s0) =>
      val (time1, s1, ea) = action(time0, s0)
      val time = Math.max(time0, time1)
      (time, s1, ea.map(f))
    }

  def mapError[E2](f: E => E2): AsyncModel[S, E2, A] =
    AsyncModel { (time0, s0) =>
      val (time1, s1, ea) = action(time0, s0)
      val time = Math.max(time0, time1)
      (time, s1, ea.leftMap(es => es.map(f)))
    }

  def flatMap[B, E0 >: E](f: A => AsyncModel[S, E0, B]): AsyncModel[S, E0, B] = {
    AsyncModel { (time0, s0) =>
      val (currentTime, s1, ea) = action(time0, s0)
      ea match {
        case Left(e) =>
          (currentTime, s1, Left(e))
        case Right(a) =>
          f(a).action(currentTime, s1)
      }
    }
  }

  def printWithState(message: Either[List[E], A] => String): AsyncModel[S, E, A] =
    AsyncModel { (time0, s0) =>
      val (time1, s1, a) = action(time0, s0)
      println(s"[time: $time1] [state: $s1] ${message(a)}")
      (time1, s1, a)
    }
}

object AsyncModel {

  def pure[S, E, A](a: A): AsyncModel[S, E, A] =
    AsyncModel((time, s) => (time, s, Right(a)))

  def async[S, E, A](a: => A): AsyncModel[S, E, A] =
    AsyncModel((time, s) => (time + 1, s, Right(a)))

  def fail[S, E, A](e: => E): AsyncModel[S, E, A] =
    AsyncModel((time, s) => (time, s, Left(List(e))))

  def asyncFail[S, E, A](e: => E): AsyncModel[S, E, A] =
    AsyncModel((time, s) => (time + 1, s, Left(List(e))))

  def parallel[S, E, A, B](actionA: AsyncModel[S, E, A], actionB: AsyncModel[S, E, B])(implicit smonoid: Monoid[S]): AsyncModel[S, E, (A, B)] =
    AsyncModel { (time0, s) =>
      val (timeA, sa, ea) = actionA.action(time0, s)
      val (timeB, sb, eb) = actionB.action(time0, s)
      val time = Math.max(timeA, timeB)
      (time, smonoid.combine(sa, sb), (ea, eb) match {
        case (Right(a), Right(b)) => Right(a -> b)
        case (Left(ae), Left(be)) => Left(ae ++ be)
        case (Left(ae), _) => Left(ae)
        case (_, Left(be)) => Left(be)
      })
    }

  def parallelAll[S, E, A](actions: List[AsyncModel[S, E, A]])(implicit smonoid: Monoid[S]): AsyncModel[S, E, List[A]] =
    AsyncModel { (time0, s0) =>
      val init: (Int, S, Either[List[E], List[A]]) = (time0, s0, Right(List.empty))
      actions.foldRight(init) { case (future, (currentTime, currentS, results)) =>
        val (nextTime, nextS, ea) = future.action(time0, s0)
        val time = Math.max(currentTime, nextTime)
        val state = smonoid.combine(currentS, nextS)
        (time, state, (results, ea) match {
          case (Left(errors), Left(moreErrors)) => Left(moreErrors ++ errors)
          case (Left(errors), _) => Left(errors)
          case (_, Left(errors)) => Left(errors)
          case (Right(results), Right(a)) => Right(a :: results)
        })
      }
    }
}

