package com.ing.baker.types

import org.scalacheck.Prop.{forAll, propBoolean}
import org.scalacheck.{Gen, Prop}

import scala.annotation.nowarn
import scala.reflect.runtime.universe.TypeTag

package object modules {

  @nowarn
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
