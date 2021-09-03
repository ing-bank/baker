package com.ing.baker.test.common

import com.ing.baker.types.Value

class IngredientAssert[Flow](
                              private val bakerAssert: BakerAssert[Flow],
                              private val value: Value,
                              private val logInfoOnError: Any => Unit
                            ) {

  def notNull(): BakerAssert[Flow] =
    is(value => assert(!value.isNull, s"expect value '$value' to be not null"))

  def isNull: BakerAssert[Flow] =
    is(value => assert(value.isNull, s"expect value '$value' to be null"))

  def isEqual[T](v: T): BakerAssert[Flow] =
    is(value => assert(value.equalsObject(v), s"""expect value $value to equal to "$v""""))

  def is(assertion: Value => Unit): BakerAssert[Flow] = {
    logInfoOnError(assertion(value))
    bakerAssert
  }
}

