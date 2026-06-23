package com.ing.baker.runtime.scaladsl

import io.circe.{Encoder, Json}
import io.circe.syntax._
import BakerResult.BakerResultCode
import com.ing.baker.runtime.common.BakerException
import com.ing.baker.runtime.serialization.JsonEncoders.bakerExceptionEncoder

case class BakerResult(result: BakerResultCode, body: Json)

object BakerResult {
  type BakerResultCode = String

  val Success: BakerResultCode = "success"
  val Error: BakerResultCode = "error"

  def apply(e: BakerException): BakerResult = new BakerResult(result = Error, e.asJson)
  def apply[A](r: A)(implicit encoder: Encoder[A]) = new BakerResult(result = Success, body = r.asJson)
  val Ack = new BakerResult(result = Success, body = Json.Null)
}

