package com.ing.baker.test.scaladsl

import com.ing.baker.types.Value

import scala.concurrent.ExecutionContext.Implicits.global

class IngredientAssert(bakerAssert: BakerAssert, name: String) {

  private val value: Value =
    bakerAssert.await(bakerAssert.baker.getIngredients(bakerAssert.recipeInstanceId)
      .map(m => m(name)))

  def notNull(): BakerAssert =
    is(value => !value.isNull)

  def isNull(): BakerAssert =
    is(value => value.isNull)

  def isEqual[T](v: T): BakerAssert =
    is(value => value.equalsObject(v))

  def is(check: Value => Boolean): BakerAssert = {
    bakerAssert.logInfoOnError(() => assert(check(value)))
    bakerAssert
  }
}

