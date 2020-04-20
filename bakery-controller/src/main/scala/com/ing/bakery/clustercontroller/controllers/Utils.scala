package com.ing.bakery.clustercontroller.controllers

import cats.effect.{IO, Timer}
import cats.syntax.apply._

import scala.concurrent.duration._

object Utils {

  /** Tries every second f until it succeeds or until 20 attempts have been made. */
  def eventually[A](f: IO[A])(implicit timer: Timer[IO]): IO[A] =
    within(60.seconds, 24)(f)

  /** Retries the argument f until it succeeds or time/split attempts have been made,
    * there exists a delay of time for each retry.
    */
  def within[A](time: FiniteDuration, split: Int)(f: IO[A])(implicit timer: Timer[IO]): IO[A] = {
    def inner(count: Int, times: FiniteDuration): IO[A] = {
      if (count < 1) f else f.attempt.flatMap {
        case Left(_) => IO.sleep(times) *> inner(count - 1, times)
        case Right(a) => IO(a)
      }
    }

    inner(split, time / split)
  }

}
