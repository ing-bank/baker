package com.ing.baker.types

import org.scalacheck.{Gen, Prop}
import org.scalacheck.Prop.forAll

import scala.reflect.runtime.universe.TypeTag


package object modules {

  def transitivityProperty[T : TypeTag](gen: Gen[T]): Prop = forAll(gen) { original =>

    // assertion of the result
    val value = Converters.toValue(original)
    val parsed = Converters.toJava[T](value)

    parsed.equals(original)
  }
}
