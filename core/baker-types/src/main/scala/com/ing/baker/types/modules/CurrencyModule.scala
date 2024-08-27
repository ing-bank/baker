package com.ing.baker.types.modules

import com.ing.baker.types._

import java.lang.reflect.{Type => JType}
import java.util.Currency

class CurrencyModule extends TypeModule {

  override def isApplicable(javaType: JType): Boolean = javaType match {
    case clazz: Class[_] if clazz.isAssignableFrom(classOf[java.util.Currency]) => true
    case _ => false
  }

  override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): Type = {
    RecordType(Seq(
      RecordField("currencyCode", CharArray),
      RecordField("defaultFractionDigits", Int32),
      RecordField("numericCode", Int32)))
  }

  override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): Any = {
    (value, javaType) match {
      case (NullValue, _) => null
      case (RecordValue(records), clazz: Class[_]) if clazz.isAssignableFrom(classOf[java.util.Currency]) && records.contains("currencyCode") =>
        java.util.Currency.getInstance(records("currencyCode").as[String])
      case _ =>
        throw new IllegalArgumentException(s"Unsupported record: $value")
    }
  }

  override def fromJava(context: TypeAdapter, obj: Any): Value = {
    obj match {
      case currency: Currency =>
        val currencyCode: String = currency.getCurrencyCode
        val defaultFractionDigits: Int = currency.getDefaultFractionDigits
        val numericCode: Int = currency.getNumericCode
        RecordValue(Map(
          "currencyCode" -> Converters.toValue(currencyCode),
          "defaultFractionDigits" -> Converters.toValue(defaultFractionDigits),
          "numericCode" -> Converters.toValue(numericCode)))
      case _ =>
        throw new IllegalArgumentException(s"Could not translate from Java object")
    }
  }
}
