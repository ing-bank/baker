package com.ing.baker.runtime.serialization

import com.ing.baker.runtime.scaladsl.IngredientInstance
import io.circe.{Codec, Decoder, Encoder, Json}
import io.circe.generic.semiauto.{deriveCodec, deriveDecoder, deriveEncoder}
import com.ing.baker.runtime.serialization.JsonEncoders._
import com.ing.baker.runtime.serialization.JsonDecoders._

object JsonCodec {

  import com.ing.baker.types._

  implicit val recordTypeCodec: Codec[RecordType] = deriveCodec[RecordType]
  implicit val mapTypeCodec: Codec[MapType] = deriveCodec[MapType]
  implicit val enumTypeCodec: Codec[EnumType] = deriveCodec[EnumType]
  implicit val optionTypeCodec: Codec[OptionType] = deriveCodec[OptionType]
  implicit val recordFieldCcodec: Codec[RecordField] = deriveCodec[RecordField]
  implicit val recordValueCodec: Codec[RecordValue] = deriveCodec[RecordValue]
  implicit val listTypeCodec: Codec[ListType] = deriveCodec[ListType]
  implicit val listValueCodec: Codec[ListValue] = deriveCodec[ListValue]
  implicit val primitiveTypeCodec: Codec[PrimitiveType] = deriveCodec[PrimitiveType]
  implicit val referenceTypeEncoder: Encoder[ReferenceType] = Encoder.encodeString.contramap[ReferenceType](_.name)
  implicit val referenceTypeDecoder: Decoder[ReferenceType] = Decoder.decodeString.map(name => ReferenceType(TypeLoader.defaultTypeLoader, name))
  implicit val typeCodec: Codec[Type] =  deriveCodec[Type]

  def removeNulls: ((String, Json)) => Boolean = {
    case (_, v) => !v.isNull
  }

  implicit val ingredientInstanceCodec: Codec[IngredientInstance] = deriveCodec[IngredientInstance]

}
