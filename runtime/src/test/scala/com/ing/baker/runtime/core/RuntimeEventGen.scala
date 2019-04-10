package com.ing.baker.runtime.core

import org.scalacheck.Gen
import com.ing.baker.runtime.actor.serialization.ProtoEventAdapterSpec

object RuntimeEventGen {

  def gen: Gen[RuntimeEvent] =
    for {
      name <- Gen.alphaNumStr
      values <- Gen.listOf(for {
        name <- Gen.alphaNumStr
        value <- ProtoEventAdapterSpec.Types.anyValueGen
      } yield (name, value))
    } yield RuntimeEvent(name, values)

}
