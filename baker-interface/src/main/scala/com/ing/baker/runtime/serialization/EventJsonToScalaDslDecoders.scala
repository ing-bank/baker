package com.ing.baker.runtime.serialization

import java.util.Base64

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.scaladsl.{BakerEvent, EventInstance, RecipeInstanceCreated}
import com.ing.baker.types
import io.circe.Decoder._
import io.circe._
import io.circe.generic.semiauto._
import io.circe.syntax._

import scala.collection.JavaConverters._

object EventJsonToScalaDslDecoders {

  implicit val eventInstanceDecoder: Decoder[EventInstance] = new Decoder[EventInstance] {
    def apply(c: HCursor): Result[EventInstance] = Right(new EventInstance("??", Map.empty))
  }

  implicit val bakerEventDecoder: Decoder[BakerEvent] = new Decoder[BakerEvent] {
    def apply(c: HCursor): Result[BakerEvent] = Right(RecipeInstanceCreated(0L, "?", "?", "?"))
  }
}