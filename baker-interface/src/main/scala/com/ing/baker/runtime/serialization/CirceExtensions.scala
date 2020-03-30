package com.ing.baker.runtime.serialization

import io.circe.Decoder.Result
import io.circe._
import io.circe.generic.extras.decoding.{ConfiguredDecoder, UnwrappedDecoder}
import io.circe.generic.extras.encoding.{ConfiguredAsObjectEncoder, UnwrappedEncoder}
import io.circe.generic.extras.{semiauto => extra}
import shapeless.Lazy

object CirceExtensions {

  trait Formatter[A] extends Decoder[A] with Encoder[A] { self =>
    def mapBoth[B](encode: Encoder[A] => Encoder[B])(decode: Decoder[A] => Decoder[B]): Formatter[B] =
      new Formatter[B] {
        override def apply(a: B): Json            = encode(self)(a)
        override def apply(c: HCursor): Result[B] = decode(self)(c)
      }
  }
  trait ObjectFormatter[A] extends Decoder[A] with Encoder.AsObject[A] with Formatter[A]

  def deriveObjectFormatter[A](encoder: Encoder.AsObject[A], decoder: Decoder[A]): ObjectFormatter[A] = new ObjectFormatter[A] {
    private val underlyingEncoder               = encoder
    private val underlyingDecoder               = decoder
    override def encodeObject(a: A): JsonObject = dropNullValuesRecursively(underlyingEncoder.encodeObject(a))
    override def apply(c: HCursor): Result[A]   = underlyingDecoder(c)
  }

  def deriveFormatter[A](encoder: Encoder[A], decoder: Decoder[A]): Formatter[A] = new Formatter[A] {
    private val underlyingEncoder             = encoder
    private val underlyingDecoder             = decoder
    override def apply(a: A): Json            = underlyingEncoder(a).mapObject(dropNullValuesRecursively)
    override def apply(c: HCursor): Result[A] = underlyingDecoder(c)
  }

  def deriveConfiguredFormatter[A](implicit encode: Lazy[ConfiguredAsObjectEncoder[A]], decode: Lazy[ConfiguredDecoder[A]]): ObjectFormatter[A] =
    deriveObjectFormatter(
      extra.deriveConfiguredEncoder[A],
      extra.deriveConfiguredDecoder[A]
    )

  def dropNullValuesRecursively(jsonObject: JsonObject): JsonObject =
    jsonObject.mapValues {
      _.mapObject(dropNullValuesRecursively)
    }.filter {
      case (_, v) => !v.isNull
    }

  implicit def formatValueClass[A](implicit encode: Lazy[UnwrappedEncoder[A]], decode: Lazy[UnwrappedDecoder[A]]): Formatter[A] =
    deriveFormatter(extra.deriveUnwrappedEncoder[A], extra.deriveUnwrappedDecoder[A])

}
