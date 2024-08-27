package com.ing.baker.types.modules

import com.ing.baker.types._

import java.time._

/**
 * Add support for Java time objects
 **/
class JavaTimeModule extends TypeModule {

  override def isApplicable(javaType: java.lang.reflect.Type): Boolean =
      isAssignableToBaseClass(javaType, classOf[java.util.Date]) ||
      isAssignableToBaseClass(javaType, classOf[LocalDate]) ||
      isAssignableToBaseClass(javaType, classOf[LocalDateTime]) ||
      isAssignableToBaseClass(javaType, classOf[OffsetDateTime]) ||
      isAssignableToBaseClass(javaType, classOf[ZonedDateTime]) ||
      isAssignableToBaseClass(javaType, classOf[Instant])

  override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): Type = Date

  override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): Any =
    (value, javaType) match {
      case (NullValue, _) => null
      case (PrimitiveValue(millis: Long), clazz: Class[_]) if classOf[java.util.Date].isAssignableFrom(clazz) =>
        java.util.Date.from(Instant.ofEpochMilli(millis))
      case (PrimitiveValue(millis: Long), clazz: Class[_]) if classOf[LocalDate].isAssignableFrom(clazz) =>
        LocalDate.ofInstant(Instant.ofEpochMilli(millis), ZoneId.systemDefault())
      case (PrimitiveValue(millis: Long), clazz: Class[_]) if classOf[LocalDateTime].isAssignableFrom(clazz) =>
        LocalDateTime.ofInstant(Instant.ofEpochMilli(millis), ZoneId.systemDefault())
      case (PrimitiveValue(millis: Long), clazz: Class[_]) if classOf[OffsetDateTime].isAssignableFrom(clazz) =>
        OffsetDateTime.ofInstant(Instant.ofEpochMilli(millis), ZoneId.systemDefault())
      case (PrimitiveValue(millis: Long), clazz: Class[_]) if classOf[ZonedDateTime].isAssignableFrom(clazz) =>
        ZonedDateTime.ofInstant(Instant.ofEpochMilli(millis), ZoneId.systemDefault())
      case (PrimitiveValue(millis: Long), clazz: Class[_]) if classOf[Instant].isAssignableFrom(clazz) =>
        Instant.ofEpochMilli(millis)
      case unsupportedType =>
        throw new IllegalArgumentException(s"UnsupportedType: $unsupportedType")
    }

  override def fromJava(context: TypeAdapter, obj: Any): Value =
    obj match {
      case date: java.util.Date => PrimitiveValue(date.toInstant.toEpochMilli)
      case localDate: LocalDate => PrimitiveValue(localDate.atStartOfDay.atZone(ZoneId.systemDefault()).toInstant.toEpochMilli)
      case localDateTime: LocalDateTime => PrimitiveValue(localDateTime.atZone(ZoneId.systemDefault()).toInstant.toEpochMilli)
      case offsetDateTime: OffsetDateTime => PrimitiveValue(offsetDateTime.toInstant.toEpochMilli)
      case zonedDateTime: ZonedDateTime => PrimitiveValue(zonedDateTime.toInstant.toEpochMilli)
      case instant: Instant => PrimitiveValue(instant.toEpochMilli)
    }
}
