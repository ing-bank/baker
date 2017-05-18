package com.ing.baker.runtime.recipe.duplicates

import scala.reflect.ClassTag

abstract class OutputTransformer[A: ClassTag, B: ClassTag] {
  def sourceType: Class[_] = implicitly[ClassTag[A]].runtimeClass

  def targetType: Class[_] = implicitly[ClassTag[B]].runtimeClass

  def fn: A ⇒ B

  def transform(a: AnyRef): B = fn(a.asInstanceOf[A])

  override def toString: String = s"${sourceType.getSimpleName} ⇒ ${targetType.getSimpleName}"
}

case class EventOutputTransformer[A: ClassTag, B: ClassTag](fn: A ⇒ B) extends OutputTransformer[A, B]