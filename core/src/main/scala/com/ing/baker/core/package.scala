package com.ing.baker

import scala.language.implicitConversions
import scala.reflect.ClassTag

package object core {

  object EventOutputTransformerOps {

    implicit def fnToEventOutputTransformer[A: ClassTag, B: ClassTag](aFunction: A ⇒ B): EventOutputTransformer[A, B] =
      EventOutputTransformer[A, B](aFunction)
  }
}
