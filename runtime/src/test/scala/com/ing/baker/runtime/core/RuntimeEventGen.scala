package com.ing.baker.runtime.core

import org.scalacheck.Gen
import com.ing.baker.types.TypesGen

object RuntimeEventGen {

  def gen: Gen[RuntimeEvent] =
    for {
      name <- Gen.alphaNumStr
      values <- Gen.listOf(for {
        name <- Gen.alphaNumStr
        value <- TypesGen.anyValueGen
      } yield (name, value))
    } yield RuntimeEvent(name, values)

}
