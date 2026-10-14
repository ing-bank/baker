package com.ing.baker.types

import com.ing.baker.types
import org.scalacheck.Gen

object TypesGen {

  import com.ing.baker.types.modules.PrimitiveModuleSpec._

  val fieldNameGen: Gen[String] = Gen.alphaStr

  val primitiveTypeGen: Gen[Type] = Gen.oneOf(types.primitiveTypes.toSeq)

  val fieldTypeGen: Gen[Type] = primitiveTypeGen

  val recordTypeEntries: Gen[RecordField] = for {
    fieldName <- fieldNameGen
    fieldType <- fieldTypeGen
  } yield RecordField(fieldName, fieldType)

  val recordTypeGen: Gen[RecordType] = Gen.listOf(recordTypeEntries).map(RecordType(_))
  val listTypeGen: Gen[ListType] = primitiveTypeGen.map(ListType)
  val mapTypeGen: Gen[MapType] = primitiveTypeGen.map(MapType)
  val optionTypeGen: Gen[OptionType] = primitiveTypeGen.map(OptionType)

  val anyTypeGen: Gen[Type] = Gen.oneOf(primitiveTypeGen, recordTypeGen, listTypeGen, mapTypeGen, optionTypeGen)

  val primitiveJavaObjGen: Gen[Any] = Gen.oneOf(
    intGen, langIntegerGen, longGen, langLongGen, shortGen, langShortGen, floatGen, langFloatGen,
    doubleGen, langDoubleGen, stringGen, bigIntGen, javaBigIntGen, bigDecimalGen, javaBigDecimalGen, byteArrayGen
  )

  val primitiveValuesGen: Gen[Value] = primitiveJavaObjGen.map(PrimitiveValue)
  val listValueGen: Gen[Value] = Gen.listOf(primitiveValuesGen).map(ListValue)
  val nullValueGen: Gen[Value] = Gen.const(NullValue)

  val recordValueEntries: Gen[(String, Value)] = for {
    fieldName <- fieldNameGen
    fieldValue <- primitiveValuesGen
  } yield fieldName -> fieldValue

  val recordValueGen: Gen[Value] = Gen.mapOf(recordValueEntries).map(RecordValue)

  val anyValueGen: Gen[Value] = Gen.oneOf(primitiveValuesGen, listValueGen, recordValueGen, nullValueGen)

  val messagesGen: Gen[AnyRef] = Gen.oneOf(anyValueGen, anyTypeGen)
}
