package com.ing.baker.types.modules

import com.ing.baker.types._

import java.time._
import java.util.{Date => JDate}
import scala.annotation.nowarn

/**
 * Add support for Java time objects
 **/
class JavaTimeModule extends TypeModule {

  override def isApplicable(javaType: java.lang.reflect.Type): Boolean =
      isAssignableToBaseClass(javaType, classOf[LocalDateTime]) ||
      isAssignableToBaseClass(javaType, classOf[LocalDate])

  override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): Type = Date

  @nowarn
  override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): Any =
    (value, javaType) match {
      case (NullValue, _) => null
      case (PrimitiveValue(millis: Long), clazz: Class[_]) if classOf[JDate].isAssignableFrom(clazz) =>
        new JDate(millis)
      case (PrimitiveValue(millis: Long), clazz: Class[_]) if classOf[LocalDateTime].isAssignableFrom(clazz) =>
        LocalDateTime.from(Instant.ofEpochMilli(millis))
      case (PrimitiveValue(millis: Long), clazz: Class[_]) if classOf[LocalDate].isAssignableFrom(clazz) =>
        LocalDate.from(Instant.ofEpochMilli(millis))
    }

  override def fromJava(context: TypeAdapter, obj: Any): Value =
    obj match {
      case date: JDate => PrimitiveValue(date.getTime)
      case localDate: LocalDate => PrimitiveValue(localDate.atStartOfDay.atZone(ZoneId.systemDefault()).toInstant
        .toEpochMilli)
      case localDateTime: LocalDateTime => PrimitiveValue(localDateTime.atZone(ZoneId.systemDefault()).toInstant.toEpochMilli)
    }
}
