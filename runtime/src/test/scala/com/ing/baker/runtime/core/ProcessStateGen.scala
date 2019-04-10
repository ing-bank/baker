package com.ing.baker.runtime.core

import com.ing.baker.runtime.actor.serialization.ProtoEventAdapterSpec
import org.scalacheck.Gen

object ProcessStateGen {

  def gen: Gen[ProcessState] =
    for {
      name <- Gen.alphaNumStr
      values <- Gen.listOf(for {
        name <- Gen.alphaNumStr
        value <- ProtoEventAdapterSpec.Types.anyValueGen
      } yield (name, value))
      eventNames <- Gen.listOf(Gen.alphaNumStr)
    } yield ProcessState(name, values.toMap, eventNames)
}
