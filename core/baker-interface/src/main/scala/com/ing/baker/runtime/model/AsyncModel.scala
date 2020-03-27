package com.ing.baker.runtime.model

import cats.kernel.Monoid
import cats.syntax.either._

case class AsyncModel[S, +E, +A](action: (Long, S) => (Long, S, Either[List[E], A])) {

  def run(implicit noState: Unit =:= S): (Long, S, Either[List[E], A]) =
    action(0, noState(()))

  def run(state0: S): (Long, S, Either[List[E], A]) =
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

  def andThen[B, E0 >: E](other: => AsyncModel[S, E0, B]): AsyncModel[S, E0, B] =
    flatMap(_ => other)

  def printWithState(message: Either[List[E], A] => String): AsyncModel[S, E, A] =
    AsyncModel { (time0, s0) =>
      val (time1, s1, a) = action(time0, s0)
      println(s"[time: $time1] [state: $s1] ${message(a)}")
      (time1, s1, a)
    }
}

object AsyncModel { module =>

  def ok[S, E, A](a: A): AsyncModel[S, E, A] =
    AsyncModel((time, s) => (time, s, Right(a)))

  def async[S, E, A](a: => A): AsyncModel[S, E, A] =
    AsyncModel((time, s) => (time + 1, s, Right(a)))

  def fail[S, E](e: => E): AsyncModel[S, E, Nothing] =
    AsyncModel((time, s) => (time, s, Left(List(e))))

  def asyncFail[S, E](e: => E): AsyncModel[S, E, Nothing] =
    AsyncModel((time, s) => (time + 1, s, Left(List(e))))

  def continue[S, E, A]: AsyncModel[S, E, Unit] =
    ok(())

  def asyncStep[S, E, A]: AsyncModel[S, E, Long] =
    async(()) andThen currentTime

  def currentTime[S, E]: AsyncModel[S, E, Long] =
    AsyncModel { (time, s) =>
      (time, s, Right(time))
    }

  def inspect[S, E]: AsyncModel[S, E, S] =
    update(identity)

  def asyncInspect[S, E]: AsyncModel[S, E, S] =
    asyncUpdate(identity)

  def stateTransition[S, E, A](f: S => (S, Either[E, A])): AsyncModel[S, E, A] =
    AsyncModel { (time, s0) =>
      val (s1, ea) = f(s0)
      (time, s1, ea.leftMap(List(_)))
    }

  def asyncStateTransition[S, E, A](f: S => (S, Either[E, A])): AsyncModel[S, E, A] =
    AsyncModel { (time, s0) =>
      val (s1, ea) = f(s0)
      (time + 1, s1, ea.leftMap(List(_)))
    }

  def update[S, E](f: S => S): AsyncModel[S, E, S] =
    AsyncModel { (time, s0) =>
      val s1 = f(s0)
      (time, s1, Right(s1))
    }

  def asyncUpdate[S, E](f: S => S): AsyncModel[S, E, S] =
    AsyncModel { (time, s0) =>
      val s1 = f(s0)
      (time + 1, s1, Right(s1))
    }

  def set[S, E](s: => S): AsyncModel[S, E, S] =
    update(_ => s)

  def asyncSet[S, E](s: => S): AsyncModel[S, E, S] =
    asyncUpdate(_ => s)

  def validate[S, E, A](ea: Either[E, A]): AsyncModel[S, E, A] =
    AsyncModel { (time, s) =>
      (time, s, ea.leftMap(List(_)))
    }

  def asyncValidate[S, E, A](ea: Either[E, A]): AsyncModel[S, E, A] =
    AsyncModel { (time, s) =>
      (time + 1, s, ea.leftMap(List(_)))
    }

  def parallelValidateAll[S, E, A](eas: List[Either[E, A]]): AsyncModel[S, E, List[A]] =
    AsyncModel { (time, s) =>
      val init: Either[List[E], List[A]] = Right(List.empty)
      val ea = eas.foldRight(init) { case (ea, results) =>
        ea -> results match {
          case (Left(e), Left(moreErrors)) => Left(e :: moreErrors)
          case (Left(e), _) => Left(List(e))
          case (_, Left(errors)) => Left(errors)
          case (Right(a), Right(as)) => Right(a :: as)
        }
      }
      (time, s, ea)
    }

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
      val init: (Long, S, Either[List[E], List[A]]) = (time0, s0, Right(List.empty))
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

  trait AsyncModelTypeSetter[S, +E] {

    def ok[A](a: A): AsyncModel[S, E, A] =
      module.ok(a)

    def async[A](a: => A): AsyncModel[S, E, A] =
      module.async(a)

    def fail[E0 >: E](e: => E0): AsyncModel[S, E0, Nothing] =
      module.fail(e)

    def asyncFail[E0 >: E](e: => E0): AsyncModel[S, E0, Nothing] =
      module.asyncFail(e)

    def continue: AsyncModel[S, E, Unit] =
      module.continue

    def asyncStep: AsyncModel[S, E, Long] =
      module.asyncStep

    def currentTime: AsyncModel[S, E, Long] =
      module.currentTime

    def inspect[A]: AsyncModel[S, E, S] =
      module.inspect

    def asyncInspect: AsyncModel[S, E, S] =
      module.asyncInspect

    def set(s: => S): AsyncModel[S, E, S] =
      module.set(s)

    def asyncSet(s: => S): AsyncModel[S, E, S] =
      module.asyncSet(s)

    def stateTransition[E0 >: E, A](f: S => (S, Either[E0, A])): AsyncModel[S, E0, A] =
      module.stateTransition(f)

    def asyncStateTransition[E0 >: E, A](f: S => (S, Either[E0, A])): AsyncModel[S, E0, A] =
      module.asyncStateTransition(f)

    def update(f: S => S): AsyncModel[S, E, S] =
      module.update(f)

    def asyncUpdate(f: S => S): AsyncModel[S, E, S] =
      module.asyncUpdate(f)

    def validate[A](ea: Either[E, A]): AsyncModel[S, E, A] =
      module.validate(ea)

    def parallel[E0 >: E, A, B](actionA: AsyncModel[S, E0, A], actionB: AsyncModel[S, E0, B])(implicit smonoid: Monoid[S]): AsyncModel[S, E0, (A, B)] =
      module.parallel(actionA, actionB)

    def parallelAll[E0 >: E, A](actions: List[AsyncModel[S, E0, A]])(implicit smonoid: Monoid[S]): AsyncModel[S, E0, List[A]] =
      module.parallelAll(actions)
  }
}
