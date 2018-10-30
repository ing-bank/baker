package com.ing.baker.types

import org.scalacheck.Prop.{BooleanOperators, forAll}
import org.scalacheck.{Gen, Prop}

import scala.reflect.runtime.universe.TypeTag

package object modules {

  def transitivityProperty[T : TypeTag](gen: Gen[T]): Prop = {

    val parsedType = Converters.readJavaType[T]

    forAll(gen) { original =>

      val value = Converters.toValue(original)
      val parsed = Converters.toJava[T](value)

      value.isInstanceOf(parsedType) :| s"$value is not an instance of $parsedType" &&
        parsed.equals(original) :| s"$value != $parsed"
    }
  }
}
