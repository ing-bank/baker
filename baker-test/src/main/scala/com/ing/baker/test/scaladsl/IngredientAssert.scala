package com.ing.baker.test.scaladsl

import com.ing.baker.types.Value

class IngredientAssert(bakerAssert: BakerAssert) {
  def notNull(): BakerAssert = ???

  def isNull(): BakerAssert = ???

  def isEqual[T](value: T): BakerAssert = ???

  def is(check: Value => Unit): BakerAssert = ???
}

