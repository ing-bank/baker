package com.ing.baker.runtime.core

import com.ing.baker.types.TypesGen
import org.scalacheck.Gen

object ProcessStateGen {

  def gen: Gen[ProcessState] =
    for {
      name <- Gen.alphaNumStr
      values <- Gen.listOf(for {
        name <- Gen.alphaNumStr
        value <- TypesGen.anyValueGen
      } yield (name, value))
      eventNames <- Gen.listOf(Gen.alphaNumStr)
    } yield ProcessState(name, values.toMap, eventNames)
}
