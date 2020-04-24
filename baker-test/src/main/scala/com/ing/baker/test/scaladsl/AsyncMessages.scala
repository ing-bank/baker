package com.ing.baker.test.scaladsl

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.{Future, Promise}
import scala.language.postfixOps

final class AsyncMessages[T] {

  @volatile var messages: Set[T] = Set.empty
  @volatile var mapping: Map[Predicate[T], Promise[T]] = Map.empty

  def put(msg: T): Unit =
    this.synchronized {
      messages = messages + msg
      mapping.keys.foreach(predicate =>
        messages.find(predicate) match {
          case Some(msg) =>
            val p = mapping(predicate)
            if (!p.isCompleted)
              p.success(msg)
          case None =>
        })
    }

  def contains(filter: Predicate[T]): Boolean =
    messages.exists(filter)

  def get(filters: Predicate[T]*): Future[Iterable[T]] =
    this.synchronized {
      if (filters.forall(messages.exists(_))) {
        Future.apply(filters.flatMap(messages.filter).toSet)
      } else {
        val mappings: Map[Predicate[T], Promise[T]] = filters.map(filter => filter -> Promise[T])
          .groupBy(_._1)
          .mapValues {
            case Seq((_, p)) => p
          }
        mapping = mapping ++ mappings
        Future.sequence(mappings.values.map(_.future).toSet)
      }
    }
}
