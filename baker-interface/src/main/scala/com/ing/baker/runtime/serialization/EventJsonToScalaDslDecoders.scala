package com.ing.baker.runtime.serialization

import com.ing.baker.runtime.scaladsl.{BakerEvent, EventInstance, RecipeInstanceCreated}
import io.circe.Decoder._
import io.circe._

object EventJsonToScalaDslDecoders {

  implicit val eventInstanceDecoder: Decoder[EventInstance] = new Decoder[EventInstance] {
    def apply(c: HCursor): Result[EventInstance] = Right(new EventInstance("??", Map.empty))
  }

  implicit val bakerEventDecoder: Decoder[BakerEvent] = new Decoder[BakerEvent] {
    def apply(c: HCursor): Result[BakerEvent] = Right(RecipeInstanceCreated(0L, "?", "?", "?"))
  }
}