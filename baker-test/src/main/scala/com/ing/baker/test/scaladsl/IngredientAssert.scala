package com.ing.baker.test.scaladsl

import com.ing.baker.types.Value

import scala.concurrent.ExecutionContext.Implicits.global

class IngredientAssert(bakerAssert: BakerAssert, name: String) {

  private val value: Value =
    bakerAssert.await(bakerAssert.baker.getIngredients(bakerAssert.recipeInstanceId)
      .map(m => m(name)))

  def notNull(): BakerAssert =
    is(value => assert(!value.isNull, s"expect value '$value' to be not null"))

  def isNull(): BakerAssert =
    is(value => assert(value.isNull, s"expect value '$value' to be null"))

  def isEqual[T](v: T): BakerAssert =
    is(value => assert(value.equalsObject(v), s"""expect value $value to equal to "$v""""))

  def is(assertion: Value => Unit): BakerAssert = {
    bakerAssert.logInfoOnError(assertion(value))
    bakerAssert
  }
}

