package com.ing.baker

import scala.language.implicitConversions
import scala.reflect.ClassTag

package object core {

  abstract class OutputTransformer[A: ClassTag, B: ClassTag] {
    def sourceType: Class[_] = implicitly[ClassTag[A]].runtimeClass

    def targetType: Class[_] = implicitly[ClassTag[B]].runtimeClass

    def fn: A ⇒ B

    def transform(a: AnyRef): B = fn(a.asInstanceOf[A])

    override def toString: String = s"${sourceType.getSimpleName} ⇒ ${targetType.getSimpleName}"
  }

  case class EventOutputTransformer[A: ClassTag, B: ClassTag](fn: A ⇒ B) extends OutputTransformer[A, B]

  object EventOutputTransformerOps {

    implicit def fnToEventOutputTransformer[A: ClassTag, B: ClassTag](aFunction: A ⇒ B): EventOutputTransformer[A, B] =
      EventOutputTransformer[A, B](aFunction)
  }

  sealed trait ActionType

  object ActionType {
    case object SieveAction       extends ActionType
    case object InteractionAction extends ActionType
  }
}
