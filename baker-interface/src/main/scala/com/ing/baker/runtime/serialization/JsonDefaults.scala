package com.ing.baker.runtime.serialization

import com.ing.baker.runtime.serialization.CirceExtensions.{Formatter, deriveFormatter}
import io.circe.generic.extras.Configuration
import io.circe.{Decoder, Encoder, Printer}

trait JsonDefaults {
  val printer: Printer                     = Printer.noSpaces.copy(dropNullValues = true)
  implicit val customConfig: Configuration = Configuration.default.withDefaults.withDiscriminator("type")

  implicit final val formatString: Formatter[String] = deriveFormatter(Encoder.encodeString, Decoder.decodeString)

}
