package com.ing.baker.runtime.common

import scala.util.{Success, Try}

object TryOps {

  object syntax {
    implicit final class IterableTryTraverseOps[A](private val values: Iterable[A]) extends AnyVal {
      def traverseTry[B](f: A => Try[B]): Try[List[B]] =
        values.foldLeft(Try(List.empty[B])) { (acc, value) =>
          for {
            items <- acc
            mapped <- f(value)
          } yield mapped :: items
        }.map(_.reverse)
    }

    implicit final class OptionTryTraverseOps[A](private val value: Option[A]) extends AnyVal {
      def traverseTry[B](f: A => Try[B]): Try[Option[B]] =
        value match {
          case Some(inner) => f(inner).map(Some(_))
          case None => Success(None)
        }
    }
  }
}

