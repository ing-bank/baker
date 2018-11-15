package com.ing.baker.petrinet

import cats.effect.IO

package object runtime {

  implicit class IOHandleErrors[T](io: IO[T]) {

    def handleException[Y >: T](pf: PartialFunction[Throwable, Y]): IO[Y] =
      io.attempt.flatMap {
        case Right(result)   => IO.pure(result)
        case Left(throwable) => pf.lift(throwable).map(IO.pure(_)).getOrElse(IO.raiseError(throwable))
      }

    def handleExceptionWith[Y >: T](pf: PartialFunction[Throwable, IO[Y]]): IO[Y] =
      io.attempt.flatMap {
        case Right(result)   => IO.pure(result)
        case Left(throwable) => pf.lift(throwable).getOrElse(IO.raiseError(throwable))
      }
  }
}
