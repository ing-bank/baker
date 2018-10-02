package com.ing.baker.types.modules

import com.ing.baker.types._
import org.joda.time._

class JodaTimeModule extends TypeModule {

  override def isApplicable(javaType: java.lang.reflect.Type): Boolean =
    isAssignableToBaseClass(javaType, classOf[DateTime]) ||
    isAssignableToBaseClass(javaType, classOf[LocalDateTime]) ||
    isAssignableToBaseClass(javaType, classOf[LocalDate])

  override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): Type = Date

  override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): Any =
    (value, javaType) match {
      case (NullValue, _) => null
      case (PrimitiveValue(millis: Long), clazz: Class[_]) if classOf[DateTime].isAssignableFrom(clazz) =>
        new DateTime(millis)
      case (PrimitiveValue(millis: Long), clazz: Class[_]) if classOf[LocalDateTime].isAssignableFrom(clazz) =>
        new LocalDateTime(millis)
      case (PrimitiveValue(millis: Long), clazz: Class[_]) if classOf[LocalDate].isAssignableFrom(clazz) =>
        new LocalDate(millis)
    }

  override def fromJava(context: TypeAdapter, obj: Any): Value =
    obj match {
      case dateTime: DateTime => PrimitiveValue(dateTime.getMillis)
      case localDate: LocalDate => PrimitiveValue(localDate.toDateTime(LocalTime.MIDNIGHT).getMillis)
      case localDateTime: LocalDateTime => PrimitiveValue(localDateTime.toDateTime.getMillis)
    }
}
